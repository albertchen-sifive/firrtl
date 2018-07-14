// See LICENSE for license details.

package firrtl
package transforms

import firrtl.Utils._
import firrtl.ir._
import firrtl.passes.ExpandConnects
import firrtl.transforms.CandidateVecFinder.CandidateVec

import scala.collection.mutable

class VecOfBoolsReplacer {
  private val candidates = new mutable.HashMap[String, (Expression, Boolean)]()
  private val fieldDelimiter = '.'
  private val tempNamePrefix = "_MY_TEMP"

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
    val tempName = namespace.newName(tempNamePrefix)
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

  private def reconnect(info: Info)(loc: Expression, expr: Expression): Seq[Statement] = {
    (loc.tpe, expr.tpe) match {
      case (g: GroundType, v: VectorType) => Seq(Connect(info, loc, vecToUInt(expr)))
      case (VectorType(BoolType, size), g: GroundType) =>
        val connects = (0 until size).map(
          i => Connect(info, SubIndex(loc, i, BoolType), onExpr(SubIndex(expr, i, BoolType))))
        connects
      case (VectorType(tpe, size), VectorType(_, _)) =>
        (0 until size).map { i =>
          Connect(info, WSubIndex(loc, i, tpe, UNKNOWNGENDER), WSubIndex(expr, i, tpe, UNKNOWNGENDER))
        }
      case (BundleType(fields1), BundleType(fields2)) => (fields1 zip fields2).flatMap { case (f1, f2) =>
        reconnect(info)(WSubField(loc, f1.name, f1.tpe, UNKNOWNGENDER),
          WSubField(expr, f2.name, f2.tpe, UNKNOWNGENDER))
      }
      case _ => Seq(Connect(info, loc, expr))
    }
  }

  private def assignSubIndices(namespace: Namespace,
                               assignments: Map[Expression, Seq[Option[Expression]]]): Seq[Statement] = {
    assignments.map { case (loc, exprs) =>
      val default = getDefault(loc)
      val value = exprs.foldLeft((EmptyExpression: Expression, 0)) {
        case ((_, 0), currExpr) => (currExpr.getOrElse(DoPrim(PrimOps.Bits, Seq(default), Seq(0, 0), BoolType)), 1)
        case ((prevExpr, idx), currExpr) =>
          (DoPrim(PrimOps.Cat,
            Seq(currExpr.getOrElse(DoPrim(PrimOps.Bits, Seq(default), Seq(idx, idx), BoolType)), prevExpr),
            Seq.empty,
            UIntType(IntWidth(idx + 1))), idx + 1)
      }._1
      assignVec(NoInfo, namespace, loc, value)
    }.toSeq
  }

  private def onStmt(namespace: Namespace,
                     pendingSubIndexConnects: mutable.HashMap[Expression, mutable.ArraySeq[Option[Expression]]])
                    (stmt: Statement): Statement = stmt match {
    case wire: DefWire => wire.mapType(replace(wire.name))
    case origReg @ DefRegister(info, name, origTpe, _, _, _) =>
      val replacedTpe = replace(name)(origTpe)
      val reg = origReg.copy(tpe = replacedTpe).mapExpr(onExpr).asInstanceOf[DefRegister]

      if (replacedTpe != reg.init.tpe) {
        val exprName = namespace.newName(tempNamePrefix)
        val exprNode = DefNode(info, exprName, reg.init)
        val expr = WRef(exprName, reg.init.tpe, WireKind, UNKNOWNGENDER)

        val locName = namespace.newName(tempNamePrefix)
        val locWire = DefWire(info, locName, replacedTpe)
        val loc = WRef(locName, replacedTpe, WireKind, UNKNOWNGENDER)

        val connects = reconnect(info)(loc, expr)

        Block(exprNode +: locWire +: reg.copy(init = loc) +: connects)
      } else {
        reg
      }

    case node @ DefNode(_, name, origValue) =>
      val valuex = onExpr(origValue)
      if (isReplaced(WRef(name)) && valuex.tpe != getDefault(WRef(name)).tpe) {
        node.copy(value = vecToUInt(valuex))
      } else {
        node.copy(value = valuex)
      }

    case Connect(_, WSubIndex(vec, index, _, _), origValue) if isReplaced(vec) =>

      val subIndexValues = pendingSubIndexConnects.getOrElseUpdate(onExpr(vec), {
        val size = vec.tpe.asInstanceOf[VectorType].size
        val values = new mutable.ArraySeq[Option[Expression]](size)
        (0 until size).foreach(values(_) = Option.empty)
        values
      })
      subIndexValues(index) = Some(onExpr(origValue))
      EmptyStmt

    case Connect(info, WSubAccess(vec, origIndex, _, _), origValue) if isReplaced(vec) =>
      val subIndexAsignments = assignSubIndices(namespace, pendingSubIndexConnects.toMap)
      pendingSubIndexConnects.clear()

      val default = getDefault(vec)
      val value = onExpr(origValue)
      val index = onExpr(origIndex)
      val subAccessAssignment = replaceAccess(namespace, info, vec, default, value, index, default.tpe)
      Block(subIndexAsignments :+ subAccessAssignment)

    case Connect(info, origExpr, origValue) if isReplaced(origExpr) =>
      val value = onExpr(origValue)
      val expr = onExpr(origExpr)
      assignVec(info, namespace, expr, vecToUInt(value))

    case Connect(info, expr, value) => Block(reconnect(info)(onExpr(expr), onExpr(value)))

    case wDefInstance: WDefInstance => wDefInstance.mapType(replace(wDefInstance.name))

    case Conditionally(info, origCond, origConseq, origAlt) =>
      val subIndexAsignments = assignSubIndices(namespace, pendingSubIndexConnects.toMap)
      pendingSubIndexConnects.clear()

      val prevDefaults = candidates.clone()
      val cond = onExpr(origCond)

      // create new wires for conditional assignments
      val conditionalDefaults = prevDefaults.collect {
        case (name, (default, _)) => (name, (WRef(namespace.newName(tempNamePrefix), default.tpe), false))
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
      val partialConseq = Seq(onStmt(namespace, pendingSubIndexConnects)(origConseq))
      val conseq = Block(partialConseq ++
        assignSubIndices(namespace, pendingSubIndexConnects.toMap) ++
        conditionalDefaults.collect {
          case (name, (default, _)) if candidates(name)._2 =>
            conditionalDefaults.put(name, (default, true))
            Connect(info, default, candidates(name)._1)
        })

      // reset defaults and flags
      pendingSubIndexConnects.clear()
      candidates ++= prevDefaults
      candidates.foreach{ case (k, (e, _)) => candidates.put(k, (e, false))}

      // do the same thing for alt block
      val alt = origAlt match {
        case EmptyStmt => origAlt
        case _ =>
          val partialAlt = Seq(onStmt(namespace, pendingSubIndexConnects)(origAlt))
          Block(partialAlt ++
            assignSubIndices(namespace, pendingSubIndexConnects.toMap) ++
            conditionalDefaults.collect {
              case (name, (default, _)) if candidates(name)._2 =>
                conditionalDefaults.put(name, (default, true))
                Connect(info, default, candidates(name)._1)
            })
      }
      pendingSubIndexConnects.clear()
      candidates ++= prevDefaults

      val conditional = Conditionally(info, cond, conseq, alt)
      conditionalDefaults.foreach {
        case (k, (default, touched)) if touched => candidates.put(k, (default, true))
        case _ =>
      }

      Block(subIndexAsignments ++: defaults :+ conditional)

    case other => other.mapStmt(onStmt(namespace, pendingSubIndexConnects)).mapExpr(onExpr)
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

    case replaced => replaced.mapType(replace(replaced.serialize))
  }

  /** Replace Vec of Bools
    *
    * Finds and replaces wire or register declarations of type Vec of bool
    * with a UInt of the same length. SubAccess/SubIndex nodes are replaced
    * with equivalent bitwise operations.
    *
    * @param mod [[Module]] to transform
    * @param candidatesx set of candidates to replace
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

    val portsx = mod.ports.map { p => p.copy(tpe = replace(p.name)(p.tpe)) }
    val pendingSubIndexConnects = new mutable.HashMap[Expression, mutable.ArraySeq[Option[Expression]]]()
    val bodyx = onStmt(namespace, pendingSubIndexConnects)(mod.body)

    val subIndexConnects = assignSubIndices(namespace, pendingSubIndexConnects.toMap)
    val finalConnects = candidates.collect {
      case (key, (default, touched)) if touched => Connect(NoInfo, keyToExpr(key), default)
    }.toSeq

    candidates.clear()

    mod.copy(ports = portsx, body = Block(bodyx +: subIndexConnects ++: finalConnects))
  }

  private def keyToExpr(name: String): Expression = {
    val path = name.split(fieldDelimiter)
    val bundleRef: Expression = WRef(path.head)
    path.tail.foldLeft(bundleRef)((expr, field) => WSubField(expr, field)).mapType(_ => candidates(name)._1.tpe)
  }
}

/** Replace Vec of Bools
  *
  * This transform replaces Vecs of Bools with UInts
  */
class ReplaceVecOfBools extends Transform {
  def inputForm: HighForm.type = HighForm
  def outputForm: HighForm.type = HighForm

  def execute(state: CircuitState): CircuitState = {
    val expandedState = ExpandConnects.execute(state)
    val renamesx = expandedState.renames.getOrElse(RenameMap())
    renamesx.setCircuit(expandedState.circuit.main)
    val replacer = new VecOfBoolsReplacer
    val candidatesMap = CandidateVecFinder.getCandidateVecs(expandedState.circuit)
    val modulesx = expandedState.circuit.modules.map {
      case mod: Module =>
        val candidates = candidatesMap(mod.name)
        if (candidates.isEmpty) {
          mod
        } else {
          renamesx.setModule(mod.name)
          candidates.foreach { candidate =>
            for (i <- 0 until candidate.tpe.size) {
              renamesx.rename(s"${candidate.name}[$i]", s"${candidate.name}")
            }
          }

          replacer.replaceVecOfBools(mod, candidates)
        }
      case ext: ExtModule => ext
    }

    val circuitState = expandedState.copy(circuit = expandedState.circuit.copy(modules = modulesx),
      renames = Some(renamesx))
    //println(circuitState.circuit.serialize)
    circuitState
  }
}
