// See LICENSE for license details.

package firrtl
package transforms

import firrtl.ir._
import firrtl.Utils._

import scala.collection.mutable

object ReplaceVecOfBools {

  private val replacedVecs = new mutable.HashMap[String, Expression]()
  private val inputs = new mutable.HashSet[String]()

  private val fieldDelimeter = '.'

  private def replaceAndRegister(name: String, isInput: Boolean = true, isPort: Boolean = false)(tpe: Type): Type = {
    tpe match {
      case VectorType(BoolType, size) =>
        if (isPort && isInput) {
          inputs.add(name)
          replacedVecs.put(name, keyToExpr(name).mapType(_ => UIntType(IntWidth(size))))
        } else {
          replacedVecs.put(name, UIntLiteral(0, IntWidth(size)))
        }
        UIntType(IntWidth(size))
      case BundleType(fields) => BundleType(fields.map { case field =>
        field.copy(tpe = replaceAndRegister(name + fieldDelimeter + field.name,
          isInput ^ field.flip == Flip,
          isPort)(field.tpe))
      })
      case other => other
    }
  }

  private def boolVecToUInt(tpe: Type): Type = {
    tpe match {
      case VectorType(BoolType, size) => UIntType(IntWidth(size))
      case BundleType(fields) => BundleType(fields.map(field => field.copy(tpe = boolVecToUInt(field.tpe))))
      case other => other
    }
  }

  private def isReplaced(expr: Expression): Boolean = expr match {
    case WRef(name, _, _, _) => replacedVecs.contains(name)
    case WSubField(WRef(instanceName, _, _, _), fieldName, _, _) =>
      replacedVecs.contains(instanceName + fieldDelimeter + fieldName)
    case _ => false
  }

  private def getDefault(expr: Expression, suffix: String = ""): Expression = expr match {
    case wRef: WRef => replacedVecs(wRef.name + suffix)
    case WSubField(WRef(name, _, _, _), fieldName, _, _) => replacedVecs(name + fieldDelimeter + fieldName)
    case WSubField(bundle, fieldName, _, _) => getDefault(bundle, fieldName + fieldName + suffix)
  }

  private def setDefault(expr: Expression, default: Expression, suffix: String = ""): Unit = expr match {
    case wRef: WRef => replacedVecs.put(wRef.name + suffix, default)
    case WSubField(WRef(name, _, _, _), fieldName, _, _) => replacedVecs.put(name + fieldDelimeter + fieldName, default)
    case WSubField(bundle, fieldName, _, _) => setDefault(bundle, default, fieldName + fieldDelimeter + suffix)
  }

  private def assignVec(info: Info, namespace: Namespace, origExpr: Expression, value: Expression): DefNode = {
    val default = getDefault(origExpr)
    val tempName = namespace.newName("temp")
    setDefault(origExpr, WRef(tempName, default.tpe))
    DefNode(info, tempName, value)
  }

  private def onStmt(namespace: Namespace)(stmt: Statement): Statement = stmt match {

    case wire: DefWire => wire.mapType(replaceAndRegister(wire.name))
    case reg: DefRegister => reg.mapType(replaceAndRegister(reg.name))

    case Connect(info, WSubIndex(wRef, index, _, _), origValue) if isReplaced(wRef) =>
      val default = getDefault(wRef)
      val value = onExpr(namespace)(origValue)
      val tpe = default.tpe

      val shiftedValue = DoPrim(PrimOps.Shl, Seq(value), Seq(index), default.tpe)

      val UIntType(IntWidth(width)) = default.tpe
      val oneHot = DoPrim(PrimOps.Shl, Seq(UIntLiteral(1, IntWidth(width))), Seq(index), tpe)
      val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
      val maskedDefault = DoPrim(PrimOps.And, Seq(default, mask), Seq.empty, tpe)

      assignVec(info, namespace, wRef, DoPrim(PrimOps.Or, Seq(maskedDefault, shiftedValue), Seq.empty, tpe))

    case Connect(info, WSubAccess(wRef, origIndex, _, _), origValue) if isReplaced(wRef) =>
      val default = getDefault(wRef)
      val value = onExpr(namespace)(origValue)
      val index = onExpr(namespace)(origIndex)
      val tpe = default.tpe

      val shiftedValue = DoPrim(PrimOps.Dshl, Seq(value, index), Seq.empty, default.tpe)

      val UIntType(IntWidth(width)) = default.tpe
      val oneHot = DoPrim(PrimOps.Dshl, Seq(UIntLiteral(1, IntWidth(width)), index), Seq.empty, tpe)
      val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
      val maskedDefault = DoPrim(PrimOps.And, Seq(default, mask), Seq.empty, tpe)

      assignVec(info, namespace, wRef, DoPrim(PrimOps.Or, Seq(maskedDefault, shiftedValue), Seq.empty, tpe))

    // replace full connects to simple wires
    case Connect(info, expr, value) if isReplaced(expr) => assignVec(info, namespace, expr, onExpr(namespace)(value))

    // add temporary wires for module ports that have been replaced
    case wDefInstance: WDefInstance => wDefInstance.mapType(replaceAndRegister(wDefInstance.name, true, true))

    case Conditionally(info, origCond, origConseq, origAlt) =>
      val replacedVecsCopy = replacedVecs.clone()
      val replacedVecsDefaults = replacedVecs.clone().map { case (name, wRef) =>
        (name, WRef(namespace.newName("temp"), getDefault(keyToExpr(name)).tpe))
      }

      val defaults = replacedVecsDefaults.filter {
        case (name, _) => !inputs.contains(name)
      }.flatMap {
        case (name, prevDefault @ WRef(tempName, tpe, _, _)) =>
          val wire = DefWire(info, tempName, UIntType(UnknownWidth))
          Seq(wire, Connect(info, prevDefault, replacedVecs(name)))
      }.toSeq
      val cond = onExpr(namespace)(origCond)

      val conseq = Block(Seq(onStmt(namespace)(origConseq)) ++
        replacedVecsDefaults.filter {
          case (name, _) => !inputs.contains(name)
        }.map { case (origName, prevDefault) => Connect(info, prevDefault, replacedVecs(origName)) })
      replacedVecs ++= replacedVecsCopy

      val alt = Block(Seq(onStmt(namespace)(origAlt)) ++
        replacedVecsDefaults.filter {
          case (name, _) => !inputs.contains(name)
        }.map { case (origName, wref) => Connect(info, wref, replacedVecs(origName)) })
      replacedVecs ++= replacedVecsDefaults

      val conditional = Conditionally(info, cond, conseq, alt)
      Block(defaults :+ conditional)

/*
    // replace connects to SubAccess/Index to module ports
    case Connect(connectInfo,
    WSubAccess(wSubField @ WSubField(WRef(instanceName, _, _, _), fieldName, _, _), origIndex, _, _),
    origExpr) if isReplaced(wSubField) =>
      val origName = instanceName + "_" + fieldName
      replaceSubAccessConnect(namespace, connectInfo, origName, origIndex, origExpr)
    case Connect(info,
    WSubIndex(wSubField @ WSubField(WRef(instanceName, _, _, _), fieldName, _, _), value, _, _),
    origExpr) if isReplaced(wSubField) =>
      val origName = instanceName + "_" + fieldName
      replaceSubIndexConnect(namespace, info, origName, value, origExpr)

    // replace full connects to module ports
    case Connect(info, wSubField @ WSubField(WRef(instanceName, _, _, _), fieldName, _, _), value) if
    isReplaced(wSubField) =>
      val origName = instanceName + fieldDelimeter + fieldName
      val tempName = namespace.newName(instanceName + "_" + fieldName)
      val tpe = getDefault(wSubField).tpe
      reassignVec(info, origName, value, tempName, tpe)

    // add temporary wires for module ports that have been replaced
    case WDefInstance(info, instanceName, module, BundleType(fields)) =>
      val newFields = fields.map { case Field(fieldName, orientation, tpe) =>
        Field(fieldName, orientation, replaceAndRegister(instanceName + fieldDelimeter + fieldName)(tpe))
      }

      val newBundleType = BundleType(newFields)
      val instanceWires = fields.filter {
        case Field(_, _, VectorType(BoolType, _)) => true
        case _ => false
      }.map {
        case Field(fieldName, orientation, VectorType(BoolType, size)) =>
          val name = namespace.newName(instanceName + fieldName)
          val tpe = UIntType(IntWidth(size))
          val subField = WSubField(WRef(instanceName, newBundleType), fieldName, tpe)
          replacedVecs.put(instanceName + fieldName, WRef(name, tpe))
          if (orientation == Flip) {
            val tempName = namespace.newName(instanceName + fieldName)
            Block(Seq(reassignVec(info, name, zero, tempName, tpe),
              DefWire(info, name, tpe),
              Connect(info, subField, WRef(name, tpe))))
          } else {
            val tempName = namespace.newName(instanceName + fieldName)
            Block(Seq(reassignVec(info, name, subField, tempName, tpe),
              DefWire(info, name, tpe),
              Connect(info, WRef(name, tpe), WRef(tempName, tpe))))
          }
      }

      Block(Seq(WDefInstance(info, instanceName, module, newBundleType)) ++ instanceWires)

    case Conditionally(info, origCond, origConseq, origAlt) =>
      val replacedVecsCopy = replacedVecs.clone()
      val replacedVecsDefaults = replacedVecs.clone().map { case (name, wRef) =>
        (name, wRef.copy(name = namespace.newName(name)))
      }

      val defaults = replacedVecsDefaults.filter {
        case (name, _) => !inputs.contains(name)
      }.flatMap {
        case (name, prevDefault @ WRef(tempName, tpe, _, _)) =>
          val wire = DefWire(info, tempName, tpe)
          Seq(wire, Connect(info, prevDefault, replacedVecs(name)))
      }.toSeq
      val cond = onExpr(namespace)(origCond)

      val conseq = Block(Seq(onStmt(namespace)(origConseq)) ++
        replacedVecsDefaults.filter {
          case (name, _) => !inputs.contains(name)
        }.map { case (origName, prevDefault) => Connect(info, prevDefault, replacedVecs(origName)) })
      replacedVecs ++= replacedVecsCopy

      val alt = Block(Seq(onStmt(namespace)(origAlt)) ++
        replacedVecsDefaults.filter {
          case (name, _) => !inputs.contains(name)
        }.map { case (origName, wref) => Connect(info, wref, replacedVecs(origName)) })
      replacedVecs ++= replacedVecsDefaults

      val conditional = Conditionally(info, cond, conseq, alt)
      Block(defaults :+ conditional)
      */
    case other => other.mapStmt(onStmt(namespace)).mapExpr(onExpr(namespace))
  }

  private def onExpr(namespace: Namespace)(expr: Expression): Expression = expr match {
    case WSubIndex(vec, value, _, _) if isReplaced(vec) =>
      val wRef = getDefault(vec)
      DoPrim(PrimOps.Bits, Seq(DoPrim(PrimOps.Shr, Seq(wRef), Seq(value), wRef.tpe)), Seq(0, 0), BoolType)
    case WSubAccess(vec, origIndex, _, _) if isReplaced(vec) =>
      val index = onExpr(namespace)(origIndex)
      val wRef = getDefault(vec)
      DoPrim(PrimOps.Bits, Seq(DoPrim(PrimOps.Dshr, Seq(wRef, index), Seq.empty, wRef.tpe)), Seq(0, 0), BoolType)
    case wRef: WRef if isReplaced(wRef) => getDefault(wRef)
    case other => other.mapExpr(onExpr(namespace))
  }

  /** Replace Vec of Bools
    *
    * Finds and replaces all wire or register declarations of type Vec of bool
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
      val tpe = replaceAndRegister(name, direction == Input, true)(origTpe)
      Port(info, name, direction, tpe)
    })

    val bodyx = onStmt(namespace)(mod.body)

    val finalConnects = replacedVecs.filterKeys(!inputs.contains(_)).map {
      case (origName, wRef) => Connect(NoInfo, keyToExpr(origName), wRef)
    }.toSeq

    replacedVecs.clear()
    inputs.clear()

    mod.copy(ports = ports, body = Block(Block(outputDefaults) +: bodyx +: finalConnects))
  }

  private def keyToExpr(name: String): Expression = {
    val path = name.split('.')
    val bundleRef: Expression = WRef(path.head, UIntType(UnknownWidth))
    path.tail.foldRight(bundleRef)( (field, expr) => WSubField(expr, field) )
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

    println(circuitState.circuit.serialize)
    new ResolveAndCheck().execute(passes.ToWorkingIR.execute(circuitState))
  }
}
