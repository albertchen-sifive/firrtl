// See LICENSE for license details.

package firrtl
package transforms

import firrtl.ir._
import firrtl.Utils._

import scala.collection.mutable

object ReplaceVecOfBools {

  private val candidates = new mutable.HashMap[String, (Expression, Boolean)]()
  private val inputs = new mutable.HashSet[String]()

  private val fieldDelimeter = '.'

  private def replaceAndRegister(name: String,
                                 isInput: Boolean = true,
                                 hasDirection: Boolean = false)(tpe: Type): Type = tpe match {
    case VectorType(BoolType, size) if  size > 0 && ((size & (size - 1)) == 0) =>
      candidates.put(name, (UIntLiteral(0, IntWidth(size)), false))
      if (hasDirection && isInput) {
        inputs.add(name)
        candidates.put(name, (keyToExpr(name).mapType(_ => UIntType(IntWidth(size))), false))
      }
      UIntType(IntWidth(size))

    case BundleType(fields) => BundleType(fields.map { field =>
      field.copy(tpe = replaceAndRegister(name + fieldDelimeter + field.name,
        isInput ^ field.flip == Flip,
        hasDirection)(field.tpe))
    })
    case other => other
  }

  private def isReplaced(expr: Expression): Boolean = candidates.contains(expr.serialize)
  private def getDefault(expr: Expression): Expression = candidates(expr.serialize)._1
  private def setDefault(expr: Expression, default: Expression): Unit = {
    candidates.put(expr.serialize, (default, true))
  }

  private def assignVec(info: Info, namespace: Namespace, origExpr: Expression, value: Expression): DefNode = {
    val default = getDefault(origExpr)
    val tempName = namespace.newTemp
    setDefault(origExpr, WRef(tempName, default.tpe))
    DefNode(info, tempName, value)
  }

  private def vecToUInt(value: Expression): Expression = {
    val VectorType(BoolType, size) = value.tpe
    val firstBit: Expression = SubIndex(value, 0, BoolType)
    (1 until size).foldLeft(firstBit)((expr, i) =>
      DoPrim(PrimOps.Cat, Seq(SubIndex(value, i, BoolType), expr), Seq.empty, UIntType(IntWidth(i + 1))))
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
                           value: Expression,
                           tpe: Type): Statement = {
    val shiftedValue = DoPrim(PrimOps.Shl, Seq(value), Seq(index), default.tpe)

    val UIntType(IntWidth(width)) = default.tpe
    val oneHot = DoPrim(PrimOps.Shl, Seq(UIntLiteral(1, IntWidth(width))), Seq(index), tpe)
    val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
    val maskedDefault = DoPrim(PrimOps.And, Seq(default, mask), Seq.empty, tpe)

    assignVec(info, namespace, vec, DoPrim(PrimOps.Or, Seq(maskedDefault, shiftedValue), Seq.empty, tpe))
  }

  private def enterScope(info: Info, namespace: Namespace) = {
    val prevDefaults = candidates.clone()

    // create new wires for conditional assignments
    val conditionalDefaults = prevDefaults.filter { case (name, _) => !inputs.contains(name) }.map {
      case (name, _) => (name, (WRef(namespace.newTemp, getDefault(keyToExpr(name)).tpe), false))
    }

    // assign new wires to current default before conditional
    val defaults = conditionalDefaults.flatMap {
      case (name, (prevDefault, _)) =>
        val wire = DefWire(info, prevDefault.name, prevDefault.tpe)
        Seq(wire, Connect(info, prevDefault, candidates(name)._1))
    }.toSeq
  }

  private def onStmt(namespace: Namespace)(stmt: Statement): Statement = stmt match {
    case wire: DefWire => wire.mapType(replaceAndRegister(wire.name))
    case reg: DefRegister => reg.mapExpr(onExpr(namespace)).mapType(replaceAndRegister(reg.name))
    case node @ DefNode(_, name, origValue) =>
      val value = onExpr(namespace)(origValue)
      replaceAndRegister(name, isInput = true, hasDirection = true)(origValue.tpe)
      if (isReplaced(WRef(name)) && value.tpe != getDefault(WRef(name)).tpe) {
        node.copy(value = vecToUInt(value))
      } else {
        node.copy(value = value)
      }

    case PartialConnect(info, WSubIndex(vec, index, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(namespace)(origValue)
      replaceIndex(namespace, info, vec, index, default, value, default.tpe)

    case PartialConnect(info, WSubAccess(vec, origIndex, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(namespace)(origValue)
      val index = onExpr(namespace)(origIndex)
      replaceAccess(namespace, info, vec, default, value, index, default.tpe)

    case PartialConnect(info, expr, value) if isReplaced(expr) =>
      assignVec(info, namespace, expr, onExpr(namespace)(value))

    case Connect(info, WSubIndex(vec, index, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(namespace)(origValue)
      replaceIndex(namespace, info, vec, index, default, value, default.tpe)

    case Connect(info, WSubAccess(vec, origIndex, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(namespace)(origValue)
      val index = onExpr(namespace)(origIndex)
      replaceAccess(namespace, info, vec, default, value, index, default.tpe)

    case Connect(info, expr, origValue) if isReplaced(expr) =>
      val value = onExpr(namespace)(origValue)
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

    case wDefInstance: WDefInstance =>
      wDefInstance.mapType(replaceAndRegister(wDefInstance.name, isInput = true, hasDirection = true))

    case Conditionally(info, origCond, origConseq, origAlt) =>
      val prevDefaults = candidates.clone()
      val cond = onExpr(namespace)(origCond)

      // create new wires for conditional assignments
      val conditionalDefaults = prevDefaults.filter { case (name, _) => !inputs.contains(name) }.map {
        case (name, _) => (name, (WRef(namespace.newTemp, getDefault(keyToExpr(name)).tpe), false))
      }

      // assign new wires to current default before conditional
      val defaults = conditionalDefaults.flatMap {
        case (name, (prevDefault, _)) =>
          val wire = DefWire(info, prevDefault.name, prevDefault.tpe)
          Seq(wire, Connect(info, prevDefault, candidates(name)._1))
      }.toSeq

      // reset flags
      candidates.foreach{ case (k, (e, _)) => candidates.put(k, (e, false))}

      // map conseq with new defaults, reassign newly created wires, then reset defaults
      val conseq = Block(Seq(onStmt(namespace)(origConseq)) ++ conditionalDefaults.filter(k => candidates(k._1)._2)
        .map { case (origName, (prevDefault, _)) =>
            conditionalDefaults.put(origName, (prevDefault, true))
            Connect(info, prevDefault, candidates(origName)._1)
        })

      // reset touched flags
      candidates ++= prevDefaults
      candidates.foreach{ case (k, (e, _)) => candidates.put(k, (e, false))}

      // do the same thing for alt block
      val alt = if (origAlt == EmptyStmt) {
        origAlt
      } else {
        Block(Seq(onStmt(namespace)(origAlt)) ++ conditionalDefaults.filter(k => candidates(k._1)._2)
        .map { case (origName, (prevDefault, _)) =>
            conditionalDefaults.put(origName, (prevDefault, true))
            Connect(info, prevDefault, candidates(origName)._1)
        })
      }
      candidates ++= prevDefaults

      val conditional = Conditionally(info, cond, conseq, alt)
      conditionalDefaults.filter(_._2._2).foreach { case (k, (default, _)) => candidates.put(k, (default, true)) }

      Block(defaults :+ conditional)

    case other => other.mapStmt(onStmt(namespace)).mapExpr(onExpr(namespace))
  }

  private def onExpr(namespace: Namespace)(expr: Expression): Expression = expr match {

    case Mux(origCond, origTval, origFval, tpe) =>
      val cond = onExpr(namespace)(origCond)
      val tval = onExpr(namespace)(origTval)
      val fval = onExpr(namespace)(origFval)
      if (tval.tpe != tpe | fval.tpe != tpe) {
        val uintFval = fval.tpe match {
          case _: VectorType => vecToUInt(fval)
          case _ => fval
        }
        val uintTval = tval.tpe match {
          case _: VectorType => vecToUInt(tval)
          case _ => tval
        }
        Mux(cond, uintTval, uintFval, uintTval.tpe)
      } else {
        Mux(cond, tval, fval, tpe)
      }

    case wSubIndex @ WSubIndex(origExpr, index, _, _) =>
      val expr = onExpr(namespace)(origExpr)
      if (expr.tpe != origExpr.tpe) {
        DoPrim(PrimOps.Bits, Seq(DoPrim(PrimOps.Shr, Seq(expr), Seq(index), expr.tpe)), Seq(0, 0), BoolType)
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

    case other =>
      if (isReplaced(other)) {
        other.mapType(_ => getDefault(other).tpe)
      } else {
        other.mapExpr(onExpr(namespace))
      }
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
  def replaceVecOfBools(mod: Module): DefModule = {
    val namespace = Namespace(mod)

    val outputDefaults = new mutable.ListBuffer[Statement]()
    val ports = mod.ports.map({ case Port(info, name, direction, origTpe) =>
      val tpe = replaceAndRegister(name, direction == Input, hasDirection = true)(origTpe)
      Port(info, name, direction, tpe)
    })

    val bodyx = onStmt(namespace)(mod.body)

    val finalConnects = candidates.filterKeys(!inputs.contains(_)).map {
      case (origName, (wRef, _)) => Connect(NoInfo, keyToExpr(origName), wRef)
    }.toSeq

    candidates.clear()
    inputs.clear()

    mod.copy(ports = ports, body = Block(Block(outputDefaults) +: bodyx +: finalConnects))
  }

  private def keyToExpr(name: String): Expression = {
    val path = name.split('.')
    val bundleRef: Expression = WRef(path.head, candidates(name)._1.tpe)
    path.tail.foldLeft(bundleRef)( (expr, field) => WSubField(expr, field) )
  }
}

/** Replace Vec of Bools
  *
  * This transform replaces Vecs of Bools with UInts
  */
class ReplaceVecOfBools extends Transform {
  def inputForm = HighForm
  def outputForm = HighForm

  def execute(state: CircuitState): CircuitState = {
    val modulesx = state.circuit.modules.map {
      case mod: Module =>
        ReplaceVecOfBools.replaceVecOfBools(mod)
      case ext: ExtModule => ext
    }

    val circuitState = state.copy(circuit = state.circuit.copy(modules = modulesx))

    new ResolveAndCheck().execute(passes.ToWorkingIR.execute(circuitState))
  }
}
