// See LICENSE for license details.

package firrtl
package transforms

import firrtl.Utils._
import firrtl.ir._
import firrtl.passes.ExpandConnects
import firrtl.transforms.CandidateVecFinder.CandidateVec

import scala.collection.mutable

object ReplaceVecOfBools {
  private val candidates = new mutable.HashMap[String, (Expression, Boolean)]()
  private val fieldDelimiter = '.'

  private def replace(name: String)(tpe: Type): Type = tpe match {
    case BundleType(fields) => BundleType(fields.map { field =>
      field.copy(tpe = replace(name + fieldDelimiter + field.name)(field.tpe))
    })
    case _ if candidates.contains(name) => candidates(name)._1.tpe
    case _ => tpe
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
      val firstBit: Expression = WSubIndex(value, 0, BoolType, UNKNOWNGENDER)
      (1 until size).foldLeft(firstBit)((expr, i) =>
        DoPrim(PrimOps.Cat,
          Seq(WSubIndex(value, i, BoolType, UNKNOWNGENDER), expr),
          Seq.empty,
          UIntType(IntWidth(i + 1))))
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

    val upperBits = DoPrim(PrimOps.Bits, Seq(default), Seq(width - 1, index + 1), UIntType(IntWidth(width - index - 1)))
    val lowerBits = DoPrim(PrimOps.Bits, Seq(default), Seq(index - 1, 0), UIntType(IntWidth(index)))

    val newValue = if (width == 1) {
      value
    } else if (index == 0) {
      DoPrim(PrimOps.Cat, Seq(upperBits, value), Seq.empty, default.tpe)
    } else if (index == (width - 1)) {
      DoPrim(PrimOps.Cat, Seq(value, lowerBits), Seq.empty, default.tpe)
    } else {
      DoPrim(PrimOps.Cat,
        Seq(upperBits, DoPrim(PrimOps.Cat, Seq(value, lowerBits), Seq.empty, UIntType(IntWidth(index + 1)))),
        Seq.empty,
        default.tpe)
    }

    assignVec(info, namespace, vec, newValue)
  }

  private def onStmt(namespace: Namespace)(stmt: Statement): Statement = stmt match {
    case wire: DefWire => wire.mapType(replace(wire.name))
    case reg @ DefRegister(info, name, origTpe, _, _, origInit) =>
      val tpex = replace(name)(origTpe)
      val initx = onExpr(origInit)
      val regx = reg.copy(tpe = tpex, init = initx)
      if (tpex.isInstanceOf[VectorType] && tpex != initx.tpe) {
        val tempName = namespace.newTemp
        val loc = WRef(tempName, tpex, RegKind, UNKNOWNGENDER)
        val VectorType(BoolType, size) = tpex

        val connects = Block((0 until size).map { i =>
          Connect(info,
            WSubIndex(loc, i, BoolType, UNKNOWNGENDER),
            DoPrim(PrimOps.Bits, Seq(initx), Seq(0, 0), BoolType))
        })

        Block(Seq(DefWire(info, tempName, tpex), connects, regx.copy(init = loc).mapExpr(onExpr)))
      } else if (tpex != initx.tpe) {
        val tempName = namespace.newTemp

        val loc = WRef(tempName, tpex, RegKind, UNKNOWNGENDER)
        val locs = create_exps(loc)

        val expr = vecToUInt(initx)
        val exps = create_exps(expr)

        val connects = Block(locs.zip(exps).zipWithIndex map { case ((l, e), i) =>
          val connect = get_flip(loc.tpe, i, Default) match {
            case Default => Connect(info, l, e)
            case Flip => Connect(info, e, l)
          }
          connect.mapExpr(onExpr)
        })
        Block(Seq(DefWire(info, tempName, tpex), connects, regx.copy(init = loc).mapExpr(onExpr)))
      } else {
        regx.mapExpr(onExpr)
      }

    case node @ DefNode(_, name, origValue) =>
      val valuex = onExpr(origValue)
      if (isReplaced(WRef(name)) && valuex.tpe != getDefault(WRef(name)).tpe) {
        node.copy(value = vecToUInt(valuex))
      } else {
        node.copy(value = valuex)
      }

    case Connect(info, WSubIndex(vec, index, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(origValue)
      replaceIndex(namespace, info, vec, index, default, value, default.tpe)

    case Connect(info, WSubAccess(vec, origIndex, _, _), origValue) if isReplaced(vec) =>
      val default = getDefault(vec)
      val value = onExpr(origValue)
      val index = onExpr(origIndex)
      replaceAccess(namespace, info, vec, default, value, index, default.tpe)

    case Connect(info, origExpr, origValue) if isReplaced(origExpr) =>
      val value = onExpr(origValue)
      val expr = onExpr(origExpr)
      assignVec(info, namespace, expr, vecToUInt(value))

    case Connect(info, expr, value) if isReplaced(value) =>
      val VectorType(BoolType, size) = expr.tpe.asInstanceOf[VectorType]
      val connects = (0 until size).map(
        i => Connect(info, SubIndex(expr, i, BoolType), onExpr(SubIndex(value, i, BoolType))))
      Block(connects)

    case wDefInstance: WDefInstance => wDefInstance.mapType(replace(wDefInstance.name))

    case Conditionally(info, origCond, origConseq, origAlt) =>
      val prevDefaults = candidates.clone()
      val cond = onExpr(origCond)

      // create new wires for conditional assignments
      val conditionalDefaults = prevDefaults.collect {
        case (name, (default, _)) => (name, (WRef(namespace.newTemp, default.tpe), false))
      }

      // assign new wires to current default before conditional
      val defaults = conditionalDefaults.flatMap {
        case (name, (condDefault, _)) =>
          val wire = DefWire(info, condDefault.name, condDefault.tpe)
          Seq(wire, Connect(info, condDefault, candidates(name)._1))
      }.toSeq

      // reset flags
      candidates.foreach { case (k, (e, _)) => candidates.put(k, (e, false)) }

      // map conseq with new defaults, reassign newly created wires
      val partialConseq = Seq(onStmt(namespace)(origConseq))
      val conseq = Block(partialConseq ++ conditionalDefaults.collect {
        case (name, (default, _)) if candidates(name)._2 =>
          conditionalDefaults.put(name, (default, true))
          Connect(info, default, candidates(name)._1)
      })

      // reset defaults and flags
      candidates ++= prevDefaults
      candidates.foreach{ case (k, (e, _)) => candidates.put(k, (e, false))}

      // do the same thing for alt block
      val alt = origAlt match {
        case EmptyStmt => origAlt
        case _ =>
          val partialAlt = Seq(onStmt(namespace)(origAlt))
          Block(partialAlt ++ conditionalDefaults.collect {
            case (name, (default, _)) if candidates(name)._2 =>
              conditionalDefaults.put(name, (default, true))
              Connect(info, default, candidates(name)._1)
          })
      }
      candidates ++= prevDefaults

      val conditional = Conditionally(info, cond, conseq, alt)
      conditionalDefaults.foreach {
        case (k, (default, touched)) if touched => candidates.put(k, (default, true))
        case _ =>
      }

      Block(defaults :+ conditional)

    case other => other.mapStmt(onStmt(namespace)).mapExpr(onExpr)
  }

  private def onExpr(expr: Expression): Expression = expr.mapExpr(onExpr) match {
    case Mux(cond, uintTval, uintFval, tpe) if uintTval.tpe != tpe | uintFval.tpe != tpe =>
      val tval = vecToUInt(uintTval)
      val fval = vecToUInt(uintFval)
      Mux(cond, tval, fval, mux_type(tval.tpe, fval.tpe))

    case WSubIndex(e, index, _, _) if e.tpe.isInstanceOf[UIntType] =>
      DoPrim(PrimOps.Bits, Seq(e), Seq(index, index), BoolType)

    case WSubAccess(e, index, _, _) if e.tpe.isInstanceOf[UIntType] =>
      DoPrim(PrimOps.Bits, Seq(DoPrim(PrimOps.Dshr, Seq(e, index), Seq.empty, e.tpe)), Seq(0, 0), BoolType)

    case replaced if isReplaced(replaced) => replaced.mapType(_ => getDefault(replaced).tpe)
    case other => other
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
  def replaceVecOfBools(mod: Module, candidatesx: Set[CandidateVec]): DefModule = {
    val namespace = Namespace(mod)
    candidatesx.foreach { c =>
      candidates.put(c.name, (UIntLiteral(0, IntWidth(c.tpe.size)), false))
      if (c.hasDefault) {
        candidates.put(c.name, (keyToExpr(c.name), false))
      }
    }

    val outputDefaults = new mutable.ListBuffer[Statement]()
    val portsx = mod.ports.map { case p @ Port(_, name, _, _) => p.copy(tpe = replace(name)(p.tpe)) }
    val bodyx = onStmt(namespace)(mod.body)

    val finalConnects = candidates.collect {
      case (key, (default, touched)) if touched => Connect(NoInfo, keyToExpr(key), default)
    }.toSeq

    printCandidates
    candidates.clear()

    mod.copy(ports = portsx, body = Block(Block(outputDefaults) +: bodyx +: finalConnects))
  }

  private def keyToExpr(name: String): Expression = {
    val path = name.split(fieldDelimiter)
    val bundleRef: Expression = WRef(path.head)
    path.tail.foldLeft(bundleRef)((expr, field) => WSubField(expr, field)).mapType(_ => candidates(name)._1.tpe)
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
    val expandedState = ExpandConnects.execute(state)
    val candidatesMap = CandidateVecFinder.getCandidateVecs(expandedState.circuit)
    val modulesx = expandedState.circuit.modules.map {
      case mod: Module =>
        val candidates = candidatesMap(mod.name)
        if (candidates.isEmpty) {
          println("NOT OPTIMIZED: " + mod.name)
          mod
        } else {
          println("optimized vec of bools: " + mod.name)
          ReplaceVecOfBools.replaceVecOfBools(mod, candidates)
        }
      case ext: ExtModule => ext
    }

    val circuitState = expandedState.copy(circuit = expandedState.circuit.copy(modules = modulesx))
    //println(circuitState.circuit.serialize)

    //new ResolveAndCheck().execute(passes.ToWorkingIR.execute(circuitState))
    circuitState
  }
}
