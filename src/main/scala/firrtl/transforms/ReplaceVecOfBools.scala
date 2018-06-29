// See LICENSE for license details.

package firrtl
package transforms

import firrtl.ir._
import firrtl.Utils._
import firrtl.passes.{Errors, ExpandConnects, InferTypes}

import scala.collection.mutable

object ReplaceVecOfBools {

  private val candidates = new mutable.HashMap[String, (Expression, Boolean)]()
  private val inputs = new mutable.HashSet[String]()

  private val fieldDelimeter = '.'
  private val badModules = new mutable.HashSet[String]()
  private val errors = new Errors()

  private def replaceAndRegister(name: String,
                                 isInput: Boolean = true,
                                 hasDirection: Boolean = false)(tpe: Type): Type = tpe match {
    case VectorType(BoolType, size) if  size > 0 && ((size & (size - 1)) == 0) =>
      candidates.put(name, (UIntLiteral(0, IntWidth(size)), false))
      if (hasDirection && isInput) {
        candidates.put(name, (keyToExpr(name).mapType(_ => UIntType(IntWidth(size))), false))
      }
      UIntType(IntWidth(size))

    case BundleType(fields) => BundleType(fields.map { field =>
      field.copy(tpe = replaceAndRegister(name + fieldDelimeter + field.name,
        isInput ^ (field.flip == Flip),
        hasDirection)(field.tpe))
    })
    case other => other
  }

  private def isReplaced(expr: Expression): Boolean = candidates.contains(expr.serialize)
  private def getDefault(expr: Expression): Expression = candidates(expr.serialize)._1
  private def setDefault(expr: Expression, default: Expression): Unit = candidates.put(expr.serialize, (default, true))

  private def assignVec(info: Info, namespace: Namespace, origExpr: Expression, value: Expression): DefNode = {
    val default = getDefault(origExpr)
    val tempName = namespace.newTemp
    setDefault(origExpr, WRef(tempName, default.tpe))
    DefNode(info, tempName, value)
  }

  private def vecToUInt(value: Expression): Expression = value.tpe match {
    case VectorType(BoolType, size) =>
      val firstBit: Expression = SubIndex(value, 0, BoolType)
      (1 until size).foldLeft(firstBit)((expr, i) =>
        DoPrim(PrimOps.Cat, Seq(SubIndex(value, i, BoolType), expr), Seq.empty, UIntType(IntWidth(i + 1))))
    case _ => value
  }

  private def replaceAccess(namespace: Namespace,
                            info: Info,
                            vec: Expression,
                            default: Expression,
                            value: Expression,
                            index: Expression,
                            tpe: Type): Statement = {
    val shiftedValue = DoPrim(PrimOps.Dshl, Seq(value, index), Seq.empty, default.tpe)

    val UIntType(IntWidth(width)) = default.tpe
    val oneHot = DoPrim(PrimOps.Dshl, Seq(UIntLiteral(1, IntWidth(width)), index), Seq.empty, tpe)
    val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
    val maskedDefault = DoPrim(PrimOps.And, Seq(default, mask), Seq.empty, tpe)

    assignVec(info, namespace, vec, DoPrim(PrimOps.Or, Seq(maskedDefault, shiftedValue), Seq.empty, tpe))
  }

  private def replaceIndex(namespace: Namespace,
                           info: Info,
                           vec: Expression,
                           index: Int,
                           default: Expression,
                           valuex: Expression,
                           tpe: Type): Statement = {

    val value = valuex.mapType(_ => BoolType)
    val UIntType(IntWidth(width)) = default.tpe

    val upperbits = DoPrim(PrimOps.Bits, Seq(default), Seq(width - 1, index + 1), UIntType(IntWidth(width - index - 1)))
    val lowerbits = DoPrim(PrimOps.Bits, Seq(default), Seq(index - 1, 0), UIntType(IntWidth(index)))

    val newValue = if (width == 1) {
      value
    } else if (index == 0) {
      DoPrim(PrimOps.Cat, Seq(upperbits, value), Seq.empty, default.tpe)
    } else if (index == (width - 1)) {
      DoPrim(PrimOps.Cat, Seq(value, lowerbits), Seq.empty, default.tpe)
    } else {
      DoPrim(PrimOps.Cat,
        Seq(upperbits, DoPrim(PrimOps.Cat, Seq(value, lowerbits), Seq.empty, UIntType(IntWidth(index + 1)))),
        Seq.empty,
        default.tpe)
    }

    assignVec(info, namespace, vec, newValue)
  }

  private def onStmt(namespace: Namespace)(stmt: Statement): Statement = stmt match {
    case wire: DefWire => wire.mapType(replaceAndRegister(wire.name))
    case reg: DefRegister =>
      val regx = reg.mapExpr(onExpr(namespace)).mapType(replaceAndRegister(reg.name))
      val regRef = WRef(reg.name)
      if (isReplaced(regRef)) {
        setDefault(regRef, regRef.copy(tpe = getDefault(regRef).tpe, kind = RegKind))
      }
      regx
    case node @ DefNode(_, name, origValue) =>
      val valuex = onExpr(namespace)(origValue)
      replaceAndRegister(name, isInput = true, hasDirection = true)(origValue.tpe)
      if (isReplaced(WRef(name)) && valuex.tpe != getDefault(WRef(name)).tpe) {
        node.copy(value = vecToUInt(valuex))
      } else {
        node.copy(value = valuex)
      }

    case Connect(info, WSubIndex(vec, index, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(namespace)(origValue)
      replaceIndex(namespace, info, vec, index, default, value, default.tpe)

    case Connect(info, WSubAccess(vec, origIndex, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(namespace)(origValue)
      val index = onExpr(namespace)(origIndex)
      replaceAccess(namespace, info, vec, default, value, index, default.tpe)

    case Connect(info, origExpr, origValue) if isReplaced(origExpr) =>
      val value = onExpr(namespace)(origValue)
      val expr = onExpr(namespace)(origExpr)
      if (isReplaced(expr) && value.tpe != getDefault(expr).tpe) {
        assignVec(info, namespace, expr, vecToUInt(value))
      } else {
        assignVec(info, namespace, expr, value)
      }

    case Connect(info, expr, value) if isReplaced(value) =>
      val VectorType(BoolType, size) = expr.tpe.asInstanceOf[VectorType]
      val connects = (0 until size).map(
        i => Connect(info, SubIndex(expr, i, BoolType), onExpr(namespace)(SubIndex(value, i, BoolType))))
      Block(connects)

    case wDefInstance: WDefInstance if !badModules.contains(wDefInstance.module) =>
      wDefInstance.mapType(replaceAndRegister(wDefInstance.name, isInput = true, hasDirection = true))

    case Conditionally(info, origCond, origConseq, origAlt) =>
      val prevDefaults = candidates.clone()
      val cond = onExpr(namespace)(origCond)

      // create new wires for conditional assignments
      val conditionalDefaults = prevDefaults.collect {
        case (name, (default, _)) => (name, (WRef(namespace.newTemp, default.tpe), false))
      }

      // assign new wires to current default before conditional
      val defaults = conditionalDefaults.flatMap {
        case (name, (condDefault, _)) =>
          val wire = DefWire(info, condDefault.name, condDefault.tpe)
          Seq(wire, Connect(info, condDefault, prevDefaults(name)._1))
      }.toSeq

      // reset flags
      candidates.foreach { case (k, (e, _)) => candidates.put(k, (e, false)) }

      // map conseq with new defaults, reassign newly created wires
      val conseq = Block(Seq(onStmt(namespace)(origConseq)) ++ conditionalDefaults.collect {
        case (name, (default, touched)) if touched => Connect(info, default, candidates(name)._1)
      })

      // reset defaults and flags
      candidates ++= prevDefaults
      candidates.foreach{ case (k, (e, _)) => candidates.put(k, (e, false))}

      // do the same thing for alt block
      val alt = origAlt match {
        case EmptyStmt => origAlt
        case _ => Block(Seq(onStmt(namespace)(origAlt)) ++ conditionalDefaults.collect {
          case (name, (default, touched)) if touched => Connect(info, default, candidates(name)._1)
        })
      }
      candidates ++= prevDefaults

      val conditional = Conditionally(info, cond, conseq, alt)
      conditionalDefaults.foreach {
        case (k, (default, touched)) if touched => candidates.put(k, (default, true))
        case _ =>
      }

      Block(defaults :+ conditional)

    case other => other.mapStmt(onStmt(namespace)).mapExpr(onExpr(namespace))
  }

  private def onExpr(namespace: Namespace)(expr: Expression): Expression = expr match {

    case origMux @ Mux(origCond, origTval, origFval, tpe) =>
      val cond = onExpr(namespace)(origCond)
      val uintTval = onExpr(namespace)(origTval)
      val uintFval = onExpr(namespace)(origFval)
      if (uintTval.tpe != tpe | uintFval.tpe != tpe) {
        val tval = vecToUInt(uintTval)
        val fval = vecToUInt(uintFval)
        Mux(cond, tval, fval, mux_type(tval.tpe, fval.tpe))
      } else {
        Mux(cond, uintTval, uintFval, tpe)
      }

    case wSubIndex @ WSubIndex(origExpr, index, _, _) =>
      val expr = onExpr(namespace)(origExpr)
      if (expr.tpe != origExpr.tpe) {
        DoPrim(PrimOps.Bits, Seq(expr), Seq(index, index), BoolType)
      } else {
        wSubIndex
      }

    case wSubAccess @ WSubAccess(origExpr, origIndex, _, _) =>
      val index = onExpr(namespace)(origIndex)
      val expr = onExpr(namespace)(origExpr)
      if (expr.tpe != origExpr.tpe) {
        DoPrim(PrimOps.Bits, Seq(DoPrim(PrimOps.Dshr, Seq(expr, index), Seq.empty, expr.tpe)), Seq(0, 0), BoolType)
      } else {
        wSubAccess
      }

    case replaced if isReplaced(replaced) => replaced.mapType(_ => getDefault(replaced).tpe)
    case other => other.mapExpr(onExpr(namespace))

  }

  /** Replace Vec of Bools
    *
    * Finds and replaces wire or register declarations of type Vec of bool
    * with a UInt of the same length. SubAccess/SubIndex nodes are replaced
    * with equivalent bitwise operations.
    *
    * @param mod [[Module]] to transform
    * @return [[Module]] with bool vecs replaced
    */
  def replaceVecOfBools(mod: Module, badModulesx: mutable.HashSet[String]): DefModule = {
    val namespace = Namespace(mod)
    badModules ++= badModulesx

    val outputDefaults = new mutable.ListBuffer[Statement]()
    val portsx = mod.ports.map({
      case p @ Port(_, name, direction, _) =>
        val tpe = replaceAndRegister(name, direction == Input, hasDirection = true)(p.tpe)
        p.copy(tpe = tpe)
    })

    val bodyx = onStmt(namespace)(mod.body)

    val finalConnects = candidates.collect {
      case (key, (default, touched)) if touched => Connect(NoInfo, keyToExpr(key), default)
    }.toSeq

    printCandidates
    candidates.clear()
    badModules.clear()

    mod.copy(ports = portsx, body = Block(Block(outputDefaults) +: bodyx +: finalConnects))
  }

  private def keyToExpr(name: String): Expression = {
    val path = name.split('.')
    val bundleRef: Expression = WRef(path.head, candidates(name)._1.tpe)
    path.tail.foldLeft(bundleRef)( (expr, field) => WSubField(expr, field) )
  }

  def printCandidates = println(candidates.keySet)
}

/** Replace Vec of Bools
  *
  * This transform replaces Vecs of Bools with UInts
  */
class ReplaceVecOfBools extends Transform {
  def inputForm = HighForm
  def outputForm = HighForm

  def execute(state: CircuitState): CircuitState = {
    val combLoopChecker = new CheckCombLoopsVecs()
    val badModules = new mutable.HashSet[String]()
    val modulesx = ExpandConnects.execute(state).circuit.modules.map {
      case mod: Module =>
        if (combLoopChecker.hasBadVecs(mod)) {
          println("NOT OPTIMIZED: " + mod.name)
          badModules.add(mod.name)
          mod
        } else {
          println("optimized vec of bools: " + mod.name)
          ReplaceVecOfBools.replaceVecOfBools(mod, badModules)
        }
      case ext: ExtModule => ext
    }

    val circuitState = state.copy(circuit = state.circuit.copy(modules = modulesx))
    //println(circuitState.circuit.serialize)

    //new ResolveAndCheck().execute(passes.ToWorkingIR.execute(circuitState))
    //InferTypes.execute(circuitState)
    circuitState
  }
}
