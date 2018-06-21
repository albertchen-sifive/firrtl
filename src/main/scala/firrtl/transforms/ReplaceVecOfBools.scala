// See LICENSE for license details.

package firrtl
package transforms

import firrtl.ir._
import firrtl.Utils._

import scala.collection.mutable

object ReplaceVecOfBools {

  private val replacedVecs = new mutable.HashMap[String, (Type, String)]()
  private val inputs = new mutable.HashSet[String]()

  private def boolToUInt(name: String)(tpe: Type): Type = {
    tpe match {
      case VectorType(BoolType, size) =>
        val uintType = UIntType(IntWidth(size))
        replacedVecs.put(name, (uintType, name))
        uintType
      case other => other
    }
  }

  private def onStmt(namespace: Namespace)(stmt: Statement): Statement = stmt.mapStmt(onStmt(namespace)) match {
    case wire: DefWire => wire.mapType(boolToUInt(wire.name))
    case reg: DefRegister => reg.mapType(boolToUInt(reg.name))
    case Connect(info, WSubAccess(WRef(origName, _, _, _), origIndex, _, _), origExpr) if
    replacedVecs.contains(origName) =>
      val index = onExpr(namespace)(origIndex)
      val expr = onExpr(namespace)(origExpr)

      val (tpe, name) = replacedVecs(origName)

      val replacedVec = WRef(name, tpe)
      val tempWireName = namespace.newName(origName)
      replacedVecs.put(origName, (tpe, tempWireName))

      val shiftedValue = DoPrim(PrimOps.Dshl, Seq(expr, index), Seq.empty, tpe)

      val UIntType(IntWidth(width)) = tpe
      val oneHot = DoPrim(PrimOps.Dshl, Seq(DoPrim(PrimOps.Pad, Seq(one), Seq(width), tpe), index), Seq.empty, tpe)
      val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
      val maskedUInt = DoPrim(PrimOps.And, Seq(replacedVec, mask), Seq.empty, tpe)

      DefNode(info, tempWireName, DoPrim(PrimOps.Or, Seq(maskedUInt, shiftedValue), Seq.empty, tpe))
    case Connect(info, WSubIndex(WRef(origName, _, _, _), value, _, _), origExpr) if replacedVecs.contains(origName) =>
      val expr = onExpr(namespace)(origExpr)

      val (tpe, name) = replacedVecs(origName)

      val replacedVec = WRef(name, tpe)
      val tempWireName = namespace.newName(origName)
      replacedVecs.put(origName, (tpe, tempWireName))

      val shiftedValue = DoPrim(PrimOps.Shl, Seq(expr), Seq(value), tpe)

      val UIntType(IntWidth(width)) = tpe
      val oneHot = DoPrim(PrimOps.Shl, Seq(DoPrim(PrimOps.Pad, Seq(one), Seq(width), tpe)), Seq(value), tpe)
      val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
      val maskedUInt = DoPrim(PrimOps.And, Seq(replacedVec, mask), Seq.empty, tpe)

      DefNode(info, tempWireName, DoPrim(PrimOps.Or, Seq(maskedUInt, shiftedValue), Seq.empty, tpe))

    case Connect(connectInfo,
    WSubAccess(WSubField(WRef(instanceName, _, _, _), fieldName, _, _), origIndex, _, _),
    origExpr) if replacedVecs.contains(instanceName + fieldName) =>
      val origName = instanceName + fieldName
      val index = onExpr(namespace)(origIndex)
      val expr = onExpr(namespace)(origExpr)

      val (tpe, name) = replacedVecs(origName)

      val replacedVec = WRef(name, tpe)
      val tempWireName = namespace.newName(origName)
      replacedVecs.put(origName, (tpe, tempWireName))

      val shiftedValue = DoPrim(PrimOps.Dshl, Seq(expr, index), Seq.empty, tpe)

      val UIntType(IntWidth(width)) = tpe
      val oneHot = DoPrim(PrimOps.Dshl, Seq(DoPrim(PrimOps.Pad, Seq(one), Seq(width), tpe), index), Seq.empty, tpe)
      val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
      val maskedUInt = DoPrim(PrimOps.And, Seq(replacedVec, mask), Seq.empty, tpe)

      DefNode(connectInfo, tempWireName, DoPrim(PrimOps.Or, Seq(maskedUInt, shiftedValue), Seq.empty, tpe))
    case Connect(info,
    WSubIndex(WSubField(WRef(instanceName, _, _, _), fieldName, _, _), value, _, _),
    origExpr) if replacedVecs.contains(instanceName + fieldName) =>
      val origName = instanceName + fieldName
      val expr = onExpr(namespace)(origExpr)

      val (tpe, name) = replacedVecs(origName)

      val replacedVec = WRef(name, tpe)
      val tempWireName = namespace.newName(origName)
      replacedVecs.put(origName, (tpe, tempWireName))

      val shiftedValue = DoPrim(PrimOps.Shl, Seq(expr), Seq(value), tpe)

      val UIntType(IntWidth(width)) = tpe
      val oneHot = DoPrim(PrimOps.Shl, Seq(DoPrim(PrimOps.Pad, Seq(one), Seq(width), tpe)), Seq(value), tpe)
      val mask = DoPrim(PrimOps.Not, Seq(oneHot), Seq.empty, tpe)
      val maskedUInt = DoPrim(PrimOps.And, Seq(replacedVec, mask), Seq.empty, tpe)

      DefNode(info, tempWireName, DoPrim(PrimOps.Or, Seq(maskedUInt, shiftedValue), Seq.empty, tpe))

    case Connect(info, WRef(origName, _, _, _), value) if replacedVecs.contains(origName) =>
      val tempName = namespace.newName(origName)
      val tpe = replacedVecs(origName)._1
      replacedVecs.put(origName, (tpe, tempName))
      DefNode(info, tempName, value)
    case Connect(info, WSubField(WRef(instanceName, _, _, _), fieldName, _, _), value) if
    replacedVecs.contains(instanceName + fieldName) =>
      val origName = instanceName + fieldName
      val tempName = namespace.newName(instanceName + fieldName)
      val tpe = replacedVecs(origName)._1
      replacedVecs.put(origName, (tpe, tempName))
      DefNode(info, tempName, value)
    case WDefInstance(info, instanceName, module, BundleType(fields)) =>
      val newFields = fields.map{case Field(fieldName, orientation, tpe) =>
        Field(fieldName, orientation, boolToUInt(instanceName + fieldName)(tpe))
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
          replacedVecs.put(instanceName + fieldName, (tpe, name))
          if (orientation == Flip) {
            Block(Seq(DefWire(info, name, tpe),
              Connect(info, subField, WRef(name, tpe))))
          } else {
            val tempName = namespace.newName(instanceName + fieldName)
            replacedVecs.put(name, (tpe, tempName))
            Block(Seq(DefNode(info, tempName, subField),
              DefWire(info, name, tpe),
              Connect(info, WRef(name, tpe), WRef(tempName, tpe))))
          }
      }

      Block(Seq(WDefInstance(info, instanceName, module, newBundleType)) ++ instanceWires)
    case other => other.mapExpr(onExpr(namespace))
  }

  private def onExpr(namespace: Namespace)(expr: Expression): Expression = expr match {
    case WSubIndex(WRef(origName, _, _, _), value, _, _) if replacedVecs.contains(origName) =>
      val (tpe, name) = replacedVecs(origName)
      DoPrim(PrimOps.And,
        Seq(DoPrim(PrimOps.Shr, Seq(WRef(name, tpe)), Seq(value), tpe), one),
        Seq.empty,
        BoolType)
    case WSubAccess(WRef(origName, _, _, _), origIndex, _, _) if replacedVecs.contains(origName) =>
      val index = onExpr(namespace)(origIndex)
      val (tpe, name) = replacedVecs(origName)
      DoPrim(PrimOps.And,
        Seq(DoPrim(PrimOps.Dshr, Seq(WRef(name, tpe), index), Seq.empty, tpe), one),
        Seq.empty,
        BoolType)
    case WSubIndex(WSubField(WRef(instanceName, _, _, _), fieldName, _, _), value, _, _) if
    replacedVecs.contains(instanceName + fieldName) =>
      val (tpe, name) = replacedVecs(instanceName + fieldName)
      DoPrim(PrimOps.And,
        Seq(DoPrim(PrimOps.Shr, Seq(WRef(name, tpe)), Seq(value), tpe), one),
        Seq.empty,
        BoolType)
    case WSubAccess(WSubField(WRef(instanceName, _, _, _), fieldName, _, _), origIndex, _, _) if
    replacedVecs.contains(instanceName + fieldName) =>
      val index = onExpr(namespace)(origIndex)
      val (tpe, name) = replacedVecs(instanceName + fieldName)
      DoPrim(PrimOps.And,
        Seq(DoPrim(PrimOps.Dshr, Seq(WRef(name, tpe), index), Seq.empty, tpe), one),
        Seq.empty,
        BoolType)
    case WRef(name, _, _, _) if replacedVecs.contains(name) =>
      WRef(replacedVecs(name)._2, replacedVecs(name)._1)
    case other =>
      other.mapExpr(onExpr(namespace))
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

    val ports = mod.ports.map({ case Port(info, name, direction, tpe) =>
      if (direction == Input) inputs.add(name)
      Port(info, name, direction, boolToUInt(name)(tpe))
    })

    val bodyx = onStmt(namespace)(mod.body)
    val finalConnects = replacedVecs.filter(i => !inputs.contains(i._1)).map {
      case (origName, (tpe, tempName)) => Connect(NoInfo, WRef(origName, tpe), WRef(tempName, tpe))
    }.toSeq

    replacedVecs.clear()
    inputs.clear()

    mod.copy(ports = ports, body = Block(bodyx +: finalConnects))
  }
}

/*
  what to use for default for inputs of module instances?
  multiple passes: first pass to collect index accesses, second to cat them together?

    inst myDummy of Top1 @[:testNestedModules1.fir@27.4]
    wire myDummyboolVec : UInt<8> @[:testNestedModules1.fir@27.4]
    myDummy.boolVec <= myDummyboolVec @[:testNestedModules1.fir@27.4]
    myDummy.select <= select @[:testNestedModules1.fir@28.4]
    node myDummyboolVec_0 = or(and(myDummyboolVec, not(shl(pad(UInt<1>("h1"), 8), 0))), shl(bits(boolVec, 0, 0), 0)) @[:testNestedModules1.fir@29.4]
    node myDummyboolVec_1 = or(and(myDummyboolVec_0, not(shl(pad(UInt<1>("h1"), 8), 1))), shl(bits(boolVec, 1, 1), 1)) @[:testNestedModules1.fir@30.4]
    node myDummyboolVec_2 = or(and(myDummyboolVec_1, not(shl(pad(UInt<1>("h1"), 8), 2))), shl(bits(boolVec, 2, 2), 2)) @[:testNestedModules1.fir@31.4]
    node myDummyboolVec_3 = or(and(myDummyboolVec_2, not(shl(pad(UInt<1>("h1"), 8), 3))), shl(bits(boolVec, 3, 3), 3)) @[:testNestedModules1.fir@32.4]
    node myDummyboolVec_4 = or(and(myDummyboolVec_3, not(shl(pad(UInt<1>("h1"), 8), 4))), shl(bits(boolVec, 4, 4), 4)) @[:testNestedModules1.fir@33.4]
    node myDummyboolVec_5 = or(and(myDummyboolVec_4, not(shl(pad(UInt<1>("h1"), 8), 5))), shl(bits(boolVec, 5, 5), 5)) @[:testNestedModules1.fir@34.4]
    node myDummyboolVec_6 = or(and(myDummyboolVec_5, not(shl(pad(UInt<1>("h1"), 8), 6))), shl(bits(boolVec, 6, 6), 6)) @[:testNestedModules1.fir@35.4]
    node myDummyboolVec_7 = or(and(myDummyboolVec_6, not(shl(pad(UInt<1>("h1"), 8), 7))), shl(bits(boolVec, 7, 7), 7)) @[:testNestedModules1.fir@36.4]
    myDummyboolVec <= myDummyboolVec_7
 */

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
