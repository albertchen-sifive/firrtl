// See LICENSE for license details.

package firrtl

package ir {
  import Utils.indent

  /** Intermediate Representation */
  sealed abstract class FirrtlNode {
    def serialize: String
  }
  
  sealed abstract class Info extends FirrtlNode {
    // default implementation
    def serialize: String = this.toString
    def ++(that: Info): Info
  }
  case object NoInfo extends Info {
    override def toString: String = ""
    def ++(that: Info): Info = that
  }
  case class FileInfo(info: StringLit) extends Info {
    override def toString: String = " @[" + info.serialize + "]"
    //scalastyle:off method.name
    def ++(that: Info): Info = if (that == NoInfo) this else MultiInfo(Seq(this, that))
  }
  case class MultiInfo(infos: Seq[Info]) extends Info {
    private def collectStringLits(info: Info): Seq[StringLit] = info match {
      case FileInfo(lit) => Seq(lit)
      case MultiInfo(seq) => seq flatMap collectStringLits
      case NoInfo => Seq.empty
    }
    override def toString: String = {
      val parts = collectStringLits(this)
      if (parts.nonEmpty) parts.map(_.serialize).mkString(" @[", " ", "]")
      else ""
    }
    //scalastyle:off method.name
    def ++(that: Info): Info = if (that == NoInfo) this else MultiInfo(infos :+ that)
  }
  object MultiInfo {
    def apply(infos: Info*) = {
      val infosx = infos.filterNot(_ == NoInfo)
      infosx.size match {
        case 0 => NoInfo
        case 1 => infosx.head
        case _ => new MultiInfo(infosx)
      }
    }
  }
  
  sealed trait HasName {
    val name: String
  }
  sealed trait HasInfo {
    val info: Info
  }
  sealed trait IsDeclaration extends HasName with HasInfo
  
  case class StringLit(string: String) extends FirrtlNode {
    /** Returns an escaped and quoted String */
    def escape: String = {
      import scala.reflect.runtime.universe._
      Literal(Constant(string)).toString
    }
    def serialize: String = {
      val str = escape
      str.slice(1, str.size - 1)
    }
    /** Format the string for Verilog */
    def verilogFormat: StringLit = {
      StringLit(string.replaceAll("%x", "%h"))
    }
    /** Returns an escaped and quoted String */
    def verilogEscape: String = {
      // normalize to turn things like ö into o
      import java.text.Normalizer
      val normalized = Normalizer.normalize(string, Normalizer.Form.NFD)
      val ascii = normalized flatMap StringLit.toASCII
      ascii.mkString("\"", "", "\"")
    }
  }
  object StringLit {
    /** Maps characters to ASCII for Verilog emission */
    private def toASCII(char: Char): List[Char] = char match {
      case nonASCII if !nonASCII.isValidByte => List('?')
      case '"' => List('\\', '"')
      case '\\' => List('\\', '\\')
      case c if c >= ' ' && c <= '~' => List(c)
      case '\n' => List('\\', 'n')
      case '\t' => List('\\', 't')
      case _ => List('?')
    }

    /** Create a StringLit from a raw parsed String */
    def unescape(raw: String): StringLit = {
      val str = StringContext.processEscapes(raw)
      StringLit(str)
    }
  }

  /** Primitive Operation
    *
    * See [[PrimOps]]
    */
  sealed abstract class PrimOp extends FirrtlNode {
    def serialize: String = this.toString
  }

  sealed abstract class Expression extends FirrtlNode {
    def tpe: Type
    def mapExpr(f: Expression => Expression): Expression
    def mapType(f: Type => Type): Expression
    def mapWidth(f: Width => Width): Expression
  }
  case class Reference(name: String, tpe: Type) extends Expression with HasName {
    def serialize: String = name
    def mapExpr(f: Expression => Expression): Expression = this
    def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
    def mapWidth(f: Width => Width): Expression = this
  }
  case class SubField(expr: Expression, name: String, tpe: Type) extends Expression with HasName {
    def serialize: String = s"${expr.serialize}.$name"
    def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
    def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
    def mapWidth(f: Width => Width): Expression = this
  }
  case class SubIndex(expr: Expression, value: Int, tpe: Type) extends Expression {
    def serialize: String = s"${expr.serialize}[$value]"
    def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
    def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
    def mapWidth(f: Width => Width): Expression = this
  }
  case class SubAccess(expr: Expression, index: Expression, tpe: Type) extends Expression {
    def serialize: String = s"${expr.serialize}[${index.serialize}]"
    def mapExpr(f: Expression => Expression): Expression =
      this.copy(expr = f(expr), index = f(index))
    def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
    def mapWidth(f: Width => Width): Expression = this
  }
  case class Mux(cond: Expression, tval: Expression, fval: Expression, tpe: Type) extends Expression {
    def serialize: String = s"mux(${cond.serialize}, ${tval.serialize}, ${fval.serialize})"
    def mapExpr(f: Expression => Expression): Expression = Mux(f(cond), f(tval), f(fval), tpe)
    def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
    def mapWidth(f: Width => Width): Expression = this
  }
  case class ValidIf(cond: Expression, value: Expression, tpe: Type) extends Expression {
    def serialize: String = s"validif(${cond.serialize}, ${value.serialize})"
    def mapExpr(f: Expression => Expression): Expression = ValidIf(f(cond), f(value), tpe)
    def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
    def mapWidth(f: Width => Width): Expression = this
  }
  sealed abstract class Literal extends Expression {
    val value: BigInt
    val width: Width
  }
  case class UIntLiteral(value: BigInt, width: Width) extends Literal {
    def tpe = UIntType(width)
    def serialize = s"""UInt${width.serialize}("h""" + value.toString(16)+ """")"""
    def mapExpr(f: Expression => Expression): Expression = this
    def mapType(f: Type => Type): Expression = this
    def mapWidth(f: Width => Width): Expression = UIntLiteral(value, f(width))
  }
  object UIntLiteral {
    def minWidth(value: BigInt): Width = IntWidth(math.max(value.bitLength, 1))
    def apply(value: BigInt): UIntLiteral = new UIntLiteral(value, minWidth(value))
  }
  case class SIntLiteral(value: BigInt, width: Width) extends Literal {
    def tpe = SIntType(width)
    def serialize = s"""SInt${width.serialize}("h""" + value.toString(16)+ """")"""
    def mapExpr(f: Expression => Expression): Expression = this
    def mapType(f: Type => Type): Expression = this
    def mapWidth(f: Width => Width): Expression = SIntLiteral(value, f(width))
  }
  object SIntLiteral {
    def minWidth(value: BigInt): Width = IntWidth(value.bitLength + 1)
    def apply(value: BigInt): SIntLiteral = new SIntLiteral(value, minWidth(value))
  }
  case class FixedLiteral(value: BigInt, width: Width, point: Width) extends Literal {
    def tpe = FixedType(width, point)
    def serialize = {
      val pstring = if(point == UnknownWidth) "" else s"<${point.serialize}>"
      s"""Fixed${width.serialize}$pstring("h${value.toString(16)}")"""
    }
    def mapExpr(f: Expression => Expression): Expression = this
    def mapType(f: Type => Type): Expression = this
    def mapWidth(f: Width => Width): Expression = FixedLiteral(value, f(width), f(point))
  }
  case class DoPrim(op: PrimOp, args: Seq[Expression], consts: Seq[BigInt], tpe: Type) extends Expression {
    def serialize: String = op.serialize + "(" +
      (args.map(_.serialize) ++ consts.map(_.toString)).mkString(", ") + ")"
    def mapExpr(f: Expression => Expression): Expression = this.copy(args = args map f)
    def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
    def mapWidth(f: Width => Width): Expression = this
  }

  sealed abstract class Statement extends FirrtlNode {
    def mapStmt(f: Statement => Statement): Statement
    def mapExpr(f: Expression => Expression): Statement
    def mapType(f: Type => Type): Statement
    def mapString(f: String => String): Statement
    def mapInfo(f: Info => Info): Statement
  }
  case class DefWire(info: Info, name: String, tpe: Type) extends Statement with IsDeclaration {
    def serialize: String = s"wire $name : ${tpe.serialize}" + info.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = this
    def mapType(f: Type => Type): Statement = DefWire(info, name, f(tpe))
    def mapString(f: String => String): Statement = DefWire(info, f(name), tpe)
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class DefRegister(
      info: Info,
      name: String,
      tpe: Type,
      clock: Expression,
      reset: Expression,
      init: Expression) extends Statement with IsDeclaration {
    def serialize: String =
      s"reg $name : ${tpe.serialize}, ${clock.serialize} with :" +
      indent("\n" + s"reset => (${reset.serialize}, ${init.serialize})" + info.serialize)
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement =
      DefRegister(info, name, tpe, f(clock), f(reset), f(init))
    def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
    def mapString(f: String => String): Statement = this.copy(name = f(name))
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))

  }
  case class DefInstance(info: Info, name: String, module: String) extends Statement with IsDeclaration {
    def serialize: String = s"inst $name of $module" + info.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = this
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = DefInstance(info, f(name), module)
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class DefMemory(
      info: Info,
      name: String,
      dataType: Type,
      depth: Int,
      writeLatency: Int,
      readLatency: Int,
      readers: Seq[String],
      writers: Seq[String],
      readwriters: Seq[String],
      // TODO: handle read-under-write
      readUnderWrite: Option[String] = None) extends Statement with IsDeclaration {
    def serialize: String =
      s"mem $name :" + info.serialize +
      indent(
        (Seq("\ndata-type => " + dataType.serialize,
            "depth => " + depth,
            "read-latency => " + readLatency,
            "write-latency => " + writeLatency) ++
            (readers map ("reader => " + _)) ++
            (writers map ("writer => " + _)) ++
            (readwriters map ("readwriter => " + _)) ++
         Seq("read-under-write => undefined")) mkString "\n")
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = this
    def mapType(f: Type => Type): Statement = this.copy(dataType = f(dataType))
    def mapString(f: String => String): Statement = this.copy(name = f(name))
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class DefNode(info: Info, name: String, value: Expression) extends Statement with IsDeclaration {
    def serialize: String = s"node $name = ${value.serialize}" + info.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = DefNode(info, name, f(value))
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = DefNode(info, f(name), value)
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class Conditionally(
      info: Info,
      pred: Expression,
      conseq: Statement,
      alt: Statement) extends Statement with HasInfo {
    def serialize: String =
      s"when ${pred.serialize} :" + info.serialize +
      indent("\n" + conseq.serialize) +
      (if (alt == EmptyStmt) ""
      else "\nelse :" + indent("\n" + alt.serialize))
    def mapStmt(f: Statement => Statement): Statement = Conditionally(info, pred, f(conseq), f(alt))
    def mapExpr(f: Expression => Expression): Statement = Conditionally(info, f(pred), conseq, alt)
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class Block(stmts: Seq[Statement]) extends Statement {
    def serialize: String = stmts map (_.serialize) mkString "\n"
    def mapStmt(f: Statement => Statement): Statement = Block(stmts map f)
    def mapExpr(f: Expression => Expression): Statement = this
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this
  }
  case class PartialConnect(info: Info, loc: Expression, expr: Expression) extends Statement with HasInfo {
    def serialize: String =  s"${loc.serialize} <- ${expr.serialize}" + info.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = PartialConnect(info, f(loc), f(expr))
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class Connect(info: Info, loc: Expression, expr: Expression) extends Statement with HasInfo {
    def serialize: String =  s"${loc.serialize} <= ${expr.serialize}" + info.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = Connect(info, f(loc), f(expr))
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class IsInvalid(info: Info, expr: Expression) extends Statement with HasInfo {
    def serialize: String =  s"${expr.serialize} is invalid" + info.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = IsInvalid(info, f(expr))
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class Attach(info: Info, exprs: Seq[Expression]) extends Statement with HasInfo {
    def serialize: String = "attach " + exprs.map(_.serialize).mkString("(", ", ", ")")
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = Attach(info, exprs map f)
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class Stop(info: Info, ret: Int, clk: Expression, en: Expression) extends Statement with HasInfo {
    def serialize: String = s"stop(${clk.serialize}, ${en.serialize}, $ret)" + info.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = Stop(info, ret, f(clk), f(en))
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case class Print(
      info: Info,
      string: StringLit,
      args: Seq[Expression],
      clk: Expression,
      en: Expression) extends Statement with HasInfo {
    def serialize: String = {
      val strs = Seq(clk.serialize, en.serialize, string.escape) ++
                 (args map (_.serialize))
      "printf(" + (strs mkString ", ") + ")" + info.serialize
    }
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = Print(info, string, args map f, f(clk), f(en))
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
  case object EmptyStmt extends Statement {
    def serialize: String = "skip"
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = this
    def mapType(f: Type => Type): Statement = this
    def mapString(f: String => String): Statement = this
    def mapInfo(f: Info => Info): Statement = this
  }

  sealed abstract class Width extends FirrtlNode {
    def +(x: Width): Width = (this, x) match {
      case (a: IntWidth, b: IntWidth) => IntWidth(a.width + b.width)
      case _ => UnknownWidth
    }
    def -(x: Width): Width = (this, x) match {
      case (a: IntWidth, b: IntWidth) => IntWidth(a.width - b.width)
      case _ => UnknownWidth
    }
    def max(x: Width): Width = (this, x) match {
      case (a: IntWidth, b: IntWidth) => IntWidth(a.width max b.width)
      case _ => UnknownWidth
    }
    def min(x: Width): Width = (this, x) match {
      case (a: IntWidth, b: IntWidth) => IntWidth(a.width min b.width)
      case _ => UnknownWidth
    }
  }
  /** Positive Integer Bit Width of a [[GroundType]] */
  object IntWidth {
    private val maxCached = 1024
    private val cache = new Array[IntWidth](maxCached + 1)
    def apply(width: BigInt): IntWidth = {
      if (0 <= width && width <= maxCached) {
        val i = width.toInt
        var w = cache(i)
        if (w eq null) {
          w = new IntWidth(width)
          cache(i) = w
        }
        w
      } else new IntWidth(width)
    }
    // For pattern matching
    def unapply(w: IntWidth): Option[BigInt] = Some(w.width)
  }
  class IntWidth(val width: BigInt) extends Width with Product {
    def serialize: String = s"<$width>"
    override def equals(that: Any) = that match {
      case w: IntWidth => width == w.width
      case _ => false
    }
    override def hashCode = width.toInt
    override def productPrefix = "IntWidth"
    override def toString = s"$productPrefix($width)"
    def copy(width: BigInt = width) = IntWidth(width)
    def canEqual(that: Any) = that.isInstanceOf[Width]
    def productArity = 1
    def productElement(int: Int) = int match {
      case 0 => width
      case _ => throw new IndexOutOfBoundsException
    }
  }
  case object UnknownWidth extends Width {
    def serialize: String = ""
  }

  /** Orientation of [[Field]] */
  sealed abstract class Orientation extends FirrtlNode
  case object Default extends Orientation {
    def serialize: String = ""
  }
  case object Flip extends Orientation {
    def serialize: String = "flip "
  }

  /** Field of [[BundleType]] */
  case class Field(name: String, flip: Orientation, tpe: Type) extends FirrtlNode with HasName {
    def serialize: String = flip.serialize + name + " : " + tpe.serialize
  }

  sealed abstract class Type extends FirrtlNode {
    def mapType(f: Type => Type): Type
    def mapWidth(f: Width => Width): Type
  }
  sealed abstract class GroundType extends Type {
    val width: Width
    def mapType(f: Type => Type): Type = this
  }
  object GroundType {
    def unapply(ground: GroundType): Option[Width] = Some(ground.width)
  }
  sealed abstract class AggregateType extends Type {
    def mapWidth(f: Width => Width): Type = this
  }
  case class UIntType(width: Width) extends GroundType {
    def serialize: String = "UInt" + width.serialize
    def mapWidth(f: Width => Width): Type = UIntType(f(width))
  }
  case class SIntType(width: Width) extends GroundType {
    def serialize: String = "SInt" + width.serialize
    def mapWidth(f: Width => Width): Type = SIntType(f(width))
  }
  case class FixedType(width: Width, point: Width) extends GroundType {
    override def serialize: String = {
      val pstring = if(point == UnknownWidth) "" else s"<${point.serialize}>"
      s"Fixed${width.serialize}$pstring"
    }
    def mapWidth(f: Width => Width): Type = FixedType(f(width), f(point))
  }
  case class BundleType(fields: Seq[Field]) extends AggregateType {
    def serialize: String = "{ " + (fields map (_.serialize) mkString ", ") + "}"
    def mapType(f: Type => Type): Type =
      BundleType(fields map (x => x.copy(tpe = f(x.tpe))))
  }
  case class VectorType(tpe: Type, size: Int) extends AggregateType {
    def serialize: String = tpe.serialize + s"[$size]"
    def mapType(f: Type => Type): Type = this.copy(tpe = f(tpe))
  }
  case object ClockType extends GroundType {
    val width = IntWidth(1)
    def serialize: String = "Clock"
    def mapWidth(f: Width => Width): Type = this
  }
  case class AnalogType(width: Width) extends GroundType {
    def serialize: String = "Analog" + width.serialize
    def mapWidth(f: Width => Width): Type = AnalogType(f(width))
  }
  case object UnknownType extends Type {
    def serialize: String = "?"
    def mapType(f: Type => Type): Type = this
    def mapWidth(f: Width => Width): Type = this
  }

  /** [[Port]] Direction */
  sealed abstract class Direction extends FirrtlNode
  case object Input extends Direction {
    def serialize: String = "input"
  }
  case object Output extends Direction {
    def serialize: String = "output"
  }

  /** [[DefModule]] Port */
  case class Port(
      info: Info,
      name: String,
      direction: Direction,
      tpe: Type) extends FirrtlNode with IsDeclaration {
    def serialize: String = s"${direction.serialize} $name : ${tpe.serialize}" + info.serialize
  }

  /** Parameters for external modules */
  sealed abstract class Param extends FirrtlNode {
    def name: String
    def serialize: String = s"parameter $name = "
  }
  /** Integer (of any width) Parameter */
  case class IntParam(name: String, value: BigInt) extends Param {
    override def serialize: String = super.serialize + value
  }
  /** IEEE Double Precision Parameter (for Verilog real) */
  case class DoubleParam(name: String, value: Double) extends Param {
    override def serialize: String = super.serialize + value
  }
  /** String Parameter */
  case class StringParam(name: String, value: StringLit) extends Param {
    override def serialize: String = super.serialize + value.escape
  }
  /** Raw String Parameter
    * Useful for Verilog type parameters
    * @note Firrtl doesn't guarantee anything about this String being legal in any backend
    */
  case class RawStringParam(name: String, value: String) extends Param {
    override def serialize: String = super.serialize + s"'${value.replace("'", "\\'")}'"
  }
  
  /** Base class for modules */
  sealed abstract class DefModule extends FirrtlNode with IsDeclaration {
    val info : Info
    val name : String
    val ports : Seq[Port]
    protected def serializeHeader(tpe: String): String =
      s"$tpe $name :${info.serialize}${indent(ports.map("\n" + _.serialize).mkString)}\n"
    def mapStmt(f: Statement => Statement): DefModule
    def mapPort(f: Port => Port): DefModule
    def mapString(f: String => String): DefModule
    def mapInfo(f: Info => Info): DefModule
  }
  /** Internal Module
    *
    * An instantiable hardware block
    */
  case class Module(info: Info, name: String, ports: Seq[Port], body: Statement) extends DefModule {
    def serialize: String = serializeHeader("module") + indent("\n" + body.serialize)
    def mapStmt(f: Statement => Statement): DefModule = this.copy(body = f(body))
    def mapPort(f: Port => Port): DefModule = this.copy(ports = ports map f)
    def mapString(f: String => String): DefModule = this.copy(name = f(name))
    def mapInfo(f: Info => Info): DefModule = this.copy(f(info))
  }
  /** External Module
    *
    * Generally used for Verilog black boxes
    * @param defname Defined name of the external module (ie. the name Firrtl will emit)
    */
  case class ExtModule(
      info: Info,
      name: String,
      ports: Seq[Port],
      defname: String,
      params: Seq[Param]) extends DefModule {
    def serialize: String = serializeHeader("extmodule") +
      indent(s"\ndefname = $defname\n" + params.map(_.serialize).mkString("\n"))
    def mapStmt(f: Statement => Statement): DefModule = this
    def mapPort(f: Port => Port): DefModule = this.copy(ports = ports map f)
    def mapString(f: String => String): DefModule = this.copy(name = f(name))
    def mapInfo(f: Info => Info): DefModule = this.copy(f(info))
  }

  case class Circuit(info: Info, modules: Seq[DefModule], main: String) extends FirrtlNode with HasInfo {
    def serialize: String =
      s"circuit $main :" + info.serialize +
      (modules map ("\n" + _.serialize) map indent mkString "\n") + "\n"
    def mapModule(f: DefModule => DefModule): Circuit = this.copy(modules = modules map f)
    def mapString(f: String => String): Circuit = this.copy(main = f(main))
    def mapInfo(f: Info => Info): Circuit = this.copy(f(info))
  }
}

package passes.memlib {
  import firrtl._
  import firrtl.ir._
  import Utils.indent

  case class DefAnnotatedMemory(
      info: Info,
      name: String,
      dataType: Type,
      depth: Int,
      writeLatency: Int,
      readLatency: Int,
      readers: Seq[String],
      writers: Seq[String],
      readwriters: Seq[String],
      readUnderWrite: Option[String],
      maskGran: Option[BigInt],
      memRef: Option[(String, String)] /* (Module, Mem) */
      //pins: Seq[Pin],
      ) extends Statement with IsDeclaration {
    def serialize: String = this.toMem.serialize
    def mapStmt(f: Statement => Statement): Statement = this
    def mapExpr(f: Expression => Expression): Statement = this
    def mapType(f: Type => Type): Statement = this.copy(dataType = f(dataType))
    def mapString(f: String => String): Statement = this.copy(name = f(name))
    def toMem = DefMemory(info, name, dataType, depth,
      writeLatency, readLatency, readers, writers,
      readwriters, readUnderWrite)
    def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  }
}

import scala.collection.Seq
import firrtl.ir._
import WrappedExpression._
import WrappedWidth._

sealed trait Kind
case object WireKind extends Kind
case object PoisonKind extends Kind
case object RegKind extends Kind
case object InstanceKind extends Kind
case object PortKind extends Kind
case object NodeKind extends Kind
case object MemKind extends Kind
case object ExpKind extends Kind

sealed trait Gender
case object MALE extends Gender
case object FEMALE extends Gender
case object BIGENDER extends Gender
case object UNKNOWNGENDER extends Gender

case class WRef(name: String, tpe: Type, kind: Kind, gender: Gender) extends Expression {
  def serialize: String = name
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapWidth(f: Width => Width): Expression = this
}
object WRef {
  /** Creates a WRef from a Wire */
  def apply(wire: DefWire): WRef = new WRef(wire.name, wire.tpe, WireKind, UNKNOWNGENDER)
  /** Creates a WRef from a Register */
  def apply(reg: DefRegister): WRef = new WRef(reg.name, reg.tpe, RegKind, UNKNOWNGENDER)
  /** Creates a WRef from a Node */
  def apply(node: DefNode): WRef = new WRef(node.name, node.value.tpe, NodeKind, MALE)
  def apply(n: String, t: Type = UnknownType, k: Kind = ExpKind): WRef = new WRef(n, t, k, UNKNOWNGENDER)
}
case class WSubField(expr: Expression, name: String, tpe: Type, gender: Gender) extends Expression {
  def serialize: String = s"${expr.serialize}.$name"
  def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapWidth(f: Width => Width): Expression = this
}
object WSubField {
  def apply(expr: Expression, n: String): WSubField = new WSubField(expr, n, Utils.field_type(expr.tpe, n), UNKNOWNGENDER)
  def apply(expr: Expression, name: String, tpe: Type): WSubField = new WSubField(expr, name, tpe, UNKNOWNGENDER)
}
case class WSubIndex(expr: Expression, value: Int, tpe: Type, gender: Gender) extends Expression {
  def serialize: String = s"${expr.serialize}[$value]"
  def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr))
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapWidth(f: Width => Width): Expression = this
}
case class WSubAccess(expr: Expression, index: Expression, tpe: Type, gender: Gender) extends Expression {
  def serialize: String = s"${expr.serialize}[${index.serialize}]"
  def mapExpr(f: Expression => Expression): Expression = this.copy(expr = f(expr), index = f(index))
  def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  def mapWidth(f: Width => Width): Expression = this
}
case object WVoid extends Expression {
  def tpe = UnknownType
  def serialize: String = "VOID"
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this
  def mapWidth(f: Width => Width): Expression = this
}
case object WInvalid extends Expression {
  def tpe = UnknownType
  def serialize: String = "INVALID"
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this
  def mapWidth(f: Width => Width): Expression = this
}
// Useful for splitting then remerging references
case object EmptyExpression extends Expression {
  def tpe = UnknownType
  def serialize: String = "EMPTY"
  def mapExpr(f: Expression => Expression): Expression = this
  def mapType(f: Type => Type): Expression = this
  def mapWidth(f: Width => Width): Expression = this
}
case class WDefInstance(info: Info, name: String, module: String, tpe: Type) extends Statement with IsDeclaration {
  def serialize: String = s"inst $name of $module" + info.serialize
  def mapExpr(f: Expression => Expression): Statement = this
  def mapStmt(f: Statement => Statement): Statement = this
  def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapInfo(f: Info => Info): Statement = this.copy(f(info))
}
object WDefInstance {
  def apply(name: String, module: String): WDefInstance = new WDefInstance(NoInfo, name, module, UnknownType)
}
case class WDefInstanceConnector(
    info: Info,
    name: String,
    module: String,
    tpe: Type,
    portCons: Seq[(Expression, Expression)]) extends Statement with IsDeclaration {
  def serialize: String = s"inst $name of $module with ${tpe.serialize} connected to " +
                          portCons.map(_._2.serialize).mkString("(", ", ", ")") + info.serialize
  def mapExpr(f: Expression => Expression): Statement =
    this.copy(portCons = portCons map { case (e1, e2) => (f(e1), f(e2)) })
  def mapStmt(f: Statement => Statement): Statement = this
  def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapInfo(f: Info => Info): Statement = this.copy(f(info))
}

// Resultant width is the same as the maximum input width
case object Addw extends PrimOp { override def toString = "addw" }
// Resultant width is the same as the maximum input width
case object Subw extends PrimOp { override def toString = "subw" }
// Resultant width is the same as input argument width
case object Dshlw extends PrimOp { override def toString = "dshlw" }
// Resultant width is the same as input argument width
case object Shlw extends PrimOp { override def toString = "shlw" }

object WrappedExpression {
  def apply(e: Expression) = new WrappedExpression(e)
  def we(e: Expression) = new WrappedExpression(e)
  def weq(e1: Expression, e2: Expression) = we(e1) == we(e2)
}
class WrappedExpression(val e1: Expression) {
  override def equals(we: Any) = we match {
    case (we: WrappedExpression) => (e1,we.e1) match {
      case (e1x: UIntLiteral, e2x: UIntLiteral) => e1x.value == e2x.value && eqw(e1x.width, e2x.width)
      case (e1x: SIntLiteral, e2x: SIntLiteral) => e1x.value == e2x.value && eqw(e1x.width, e2x.width)
      case (e1x: WRef, e2x: WRef) => e1x.name equals e2x.name
      case (e1x: WSubField, e2x: WSubField) => (e1x.name equals e2x.name) && weq(e1x.expr,e2x.expr)
      case (e1x: WSubIndex, e2x: WSubIndex) => (e1x.value == e2x.value) && weq(e1x.expr,e2x.expr)
      case (e1x: WSubAccess, e2x: WSubAccess) => weq(e1x.index,e2x.index) && weq(e1x.expr,e2x.expr)
      case (WVoid, WVoid) => true
      case (WInvalid, WInvalid) => true
      case (e1x: DoPrim, e2x: DoPrim) => e1x.op == e2x.op &&
         ((e1x.consts zip e2x.consts) forall {case (x, y) => x == y}) &&
         ((e1x.args zip e2x.args) forall {case (x, y) => weq(x, y)})
      case (e1x: Mux, e2x: Mux) => weq(e1x.cond,e2x.cond) && weq(e1x.tval,e2x.tval) && weq(e1x.fval,e2x.fval)
      case (e1x: ValidIf, e2x: ValidIf) => weq(e1x.cond,e2x.cond) && weq(e1x.value,e2x.value)
      case (e1x, e2x) => false
    }
    case _ => false
  }
  override def hashCode = e1.serialize.hashCode
  override def toString = e1.serialize
}

private[firrtl] sealed trait HasMapWidth {
  def mapWidth(f: Width => Width): Width
}
case class VarWidth(name: String) extends Width with HasMapWidth {
  def serialize: String = name
  def mapWidth(f: Width => Width): Width = this
}
case class PlusWidth(arg1: Width, arg2: Width) extends Width with HasMapWidth {
  def serialize: String = "(" + arg1.serialize + " + " + arg2.serialize + ")"
  def mapWidth(f: Width => Width): Width = PlusWidth(f(arg1), f(arg2))
}
case class MinusWidth(arg1: Width, arg2: Width) extends Width with HasMapWidth {
  def serialize: String = "(" + arg1.serialize + " - " + arg2.serialize + ")"
  def mapWidth(f: Width => Width): Width = MinusWidth(f(arg1), f(arg2))
}
case class MaxWidth(args: Seq[Width]) extends Width with HasMapWidth {
  def serialize: String = args map (_.serialize) mkString ("max(", ", ", ")")
  def mapWidth(f: Width => Width): Width = MaxWidth(args map f)
}
case class MinWidth(args: Seq[Width]) extends Width with HasMapWidth {
  def serialize: String = args map (_.serialize) mkString ("min(", ", ", ")")
  def mapWidth(f: Width => Width): Width = MinWidth(args map f)
}
case class ExpWidth(arg1: Width) extends Width with HasMapWidth {
  def serialize: String = "exp(" + arg1.serialize + " )"
  def mapWidth(f: Width => Width): Width = ExpWidth(f(arg1))
}

object WrappedType {
  def apply(t: Type) = new WrappedType(t)
  def wt(t: Type) = apply(t)
}
class WrappedType(val t: Type) {
  def wt(tx: Type) = new WrappedType(tx)
  override def equals(o: Any): Boolean = o match {
    case (t2: WrappedType) => (t, t2.t) match {
      case (_: UIntType, _: UIntType) => true
      case (_: SIntType, _: SIntType) => true
      case (ClockType, ClockType) => true
      case (_: FixedType, _: FixedType) => true
      // Analog totally skips out of the Firrtl type system.
      // The only way Analog can play with another Analog component is through Attach.
      // Ohterwise, we'd need to special case it during ExpandWhens, Lowering,
      // ExpandConnects, etc.
      case (_: AnalogType, _: AnalogType) => false
      case (t1: VectorType, t2: VectorType) =>
        t1.size == t2.size && wt(t1.tpe) == wt(t2.tpe)
      case (t1: BundleType, t2: BundleType) =>
        t1.fields.size == t2.fields.size && (
        (t1.fields zip t2.fields) forall { case (f1, f2) =>
          f1.flip == f2.flip && f1.name == f2.name
        }) && ((t1.fields zip t2.fields) forall { case (f1, f2) =>
          wt(f1.tpe) == wt(f2.tpe)
        })
      case _ => false
    }
    case _ => false
  }
}

object WrappedWidth {
  def eqw(w1: Width, w2: Width): Boolean = new WrappedWidth(w1) == new WrappedWidth(w2)
}

class WrappedWidth (val w: Width) {
  def ww(w: Width): WrappedWidth = new WrappedWidth(w)
  override def toString = w match {
    case (w: VarWidth) => w.name
    case (w: MaxWidth) => s"max(${w.args.mkString})"
    case (w: MinWidth) => s"min(${w.args.mkString})"
    case (w: PlusWidth) => s"(${w.arg1} + ${w.arg2})"
    case (w: MinusWidth) => s"(${w.arg1} -${w.arg2})"
    case (w: ExpWidth) => s"exp(${w.arg1})"
    case (w: IntWidth) => w.width.toString
    case UnknownWidth => "?"
  }
  override def equals(o: Any): Boolean = o match {
    case (w2: WrappedWidth) => (w, w2.w) match {
      case (w1: VarWidth, w2: VarWidth) => w1.name.equals(w2.name)
      case (w1: MaxWidth, w2: MaxWidth) => w1.args.size == w2.args.size &&
        (w1.args forall (a1 => w2.args exists (a2 => eqw(a1, a2))))
      case (w1: MinWidth, w2: MinWidth) => w1.args.size == w2.args.size &&
        (w1.args forall (a1 => w2.args exists (a2 => eqw(a1, a2))))
      case (w1: IntWidth, w2: IntWidth) => w1.width == w2.width
      case (w1: PlusWidth, w2: PlusWidth) =>
        (ww(w1.arg1) == ww(w2.arg1) && ww(w1.arg2) == ww(w2.arg2)) ||
        (ww(w1.arg1) == ww(w2.arg2) && ww(w1.arg2) == ww(w2.arg1))
      case (w1: MinusWidth,w2: MinusWidth) =>
        (ww(w1.arg1) == ww(w2.arg1) && ww(w1.arg2) == ww(w2.arg2)) ||
        (ww(w1.arg1) == ww(w2.arg2) && ww(w1.arg2) == ww(w2.arg1))
      case (w1: ExpWidth, w2: ExpWidth) => ww(w1.arg1) == ww(w2.arg1)
      case (UnknownWidth, UnknownWidth) => true
      case _ => false
    }
    case _ => false
  }
}

sealed trait Constraint
class WGeq(val loc: Width, val exp: Width) extends Constraint {
  override def toString = {
    val wloc = new WrappedWidth(loc)
    val wexp = new WrappedWidth(exp)
    wloc.toString + " >= " + wexp.toString
  }
}
object WGeq {
  def apply(loc: Width, exp: Width) = new WGeq(loc, exp)
}

sealed abstract class MPortDir extends FirrtlNode
case object MInfer extends MPortDir {
  def serialize: String = "infer"
}
case object MRead extends MPortDir {
  def serialize: String = "read"
}
case object MWrite extends MPortDir {
  def serialize: String = "write"
}
case object MReadWrite extends MPortDir {
  def serialize: String = "rdwr"
}

case class CDefMemory(
    info: Info,
    name: String,
    tpe: Type,
    size: Int,
    seq: Boolean) extends Statement with HasInfo {
  def serialize: String = (if (seq) "smem" else "cmem") +
    s" $name : ${tpe.serialize} [$size]" + info.serialize
  def mapExpr(f: Expression => Expression): Statement = this
  def mapStmt(f: Statement => Statement): Statement = this
  def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapInfo(f: Info => Info): Statement = this.copy(f(info))
}
case class CDefMPort(info: Info,
    name: String,
    tpe: Type,
    mem: String,
    exps: Seq[Expression],
    direction: MPortDir) extends Statement with HasInfo {
  def serialize: String = {
    val dir = direction.serialize
    s"$dir mport $name = $mem[${exps.head.serialize}], ${exps(1).serialize}" + info.serialize
  }
  def mapExpr(f: Expression => Expression): Statement = this.copy(exps = exps map f)
  def mapStmt(f: Statement => Statement): Statement = this
  def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapInfo(f: Info => Info): Statement = this.copy(f(info))
}

import com.typesafe.scalalogging.LazyLogging

/** Definitions and Utility functions for [[ir.PrimOp]]s */
object PrimOps extends LazyLogging {
  /** Addition */
  case object Add extends PrimOp { override def toString = "add" }
  /** Subtraction */
  case object Sub extends PrimOp { override def toString = "sub" }
  /** Multiplication */
  case object Mul extends PrimOp { override def toString = "mul" }
  /** Division */
  case object Div extends PrimOp { override def toString = "div" }
  /** Remainder */
  case object Rem extends PrimOp { override def toString = "rem" }
  /** Less Than */
  case object Lt extends PrimOp { override def toString = "lt" }
  /** Less Than Or Equal To */
  case object Leq extends PrimOp { override def toString = "leq" }
  /** Greater Than */
  case object Gt extends PrimOp { override def toString = "gt" }
  /** Greater Than Or Equal To */
  case object Geq extends PrimOp { override def toString = "geq" }
  /** Equal To */
  case object Eq extends PrimOp { override def toString = "eq" }
  /** Not Equal To */
  case object Neq extends PrimOp { override def toString = "neq" }
  /** Padding */
  case object Pad extends PrimOp { override def toString = "pad" }
  /** Interpret As UInt */
  case object AsUInt extends PrimOp { override def toString = "asUInt" }
  /** Interpret As SInt */
  case object AsSInt extends PrimOp { override def toString = "asSInt" }
  /** Interpret As Clock */
  case object AsClock extends PrimOp { override def toString = "asClock" }
  /** Static Shift Left */
  case object Shl extends PrimOp { override def toString = "shl" }
  /** Static Shift Right */
  case object Shr extends PrimOp { override def toString = "shr" }
  /** Dynamic Shift Left */
  case object Dshl extends PrimOp { override def toString = "dshl" }
  /** Dynamic Shift Right */
  case object Dshr extends PrimOp { override def toString = "dshr" }
  /** Arithmetic Convert to Signed */
  case object Cvt extends PrimOp { override def toString = "cvt" }
  /** Negate */
  case object Neg extends PrimOp { override def toString = "neg" }
  /** Bitwise Complement */
  case object Not extends PrimOp { override def toString = "not" }
  /** Bitwise And */
  case object And extends PrimOp { override def toString = "and" }
  /** Bitwise Or */
  case object Or extends PrimOp { override def toString = "or" }
  /** Bitwise Exclusive Or */
  case object Xor extends PrimOp { override def toString = "xor" }
  /** Bitwise And Reduce */
  case object Andr extends PrimOp { override def toString = "andr" }
  /** Bitwise Or Reduce */
  case object Orr extends PrimOp { override def toString = "orr" }
  /** Bitwise Exclusive Or Reduce */
  case object Xorr extends PrimOp { override def toString = "xorr" }
  /** Concatenate */
  case object Cat extends PrimOp { override def toString = "cat" }
  /** Bit Extraction */
  case object Bits extends PrimOp { override def toString = "bits" }
  /** Head */
  case object Head extends PrimOp { override def toString = "head" }
  /** Tail */
  case object Tail extends PrimOp { override def toString = "tail" }
  /** Interpret as Fixed Point **/
  case object AsFixedPoint extends PrimOp { override def toString = "asFixedPoint" }
  /** Shift Binary Point Left **/
  case object BPShl extends PrimOp { override def toString = "bpshl" }
  /** Shift Binary Point Right **/
  case object BPShr extends PrimOp { override def toString = "bpshr" }
  /** Set Binary Point **/
  case object BPSet extends PrimOp { override def toString = "bpset" }

  private lazy val builtinPrimOps: Seq[PrimOp] =
    Seq(Add, Sub, Mul, Div, Rem, Lt, Leq, Gt, Geq, Eq, Neq, Pad, AsUInt, AsSInt, AsClock, Shl, Shr,
        Dshl, Dshr, Neg, Cvt, Not, And, Or, Xor, Andr, Orr, Xorr, Cat, Bits, Head, Tail, AsFixedPoint, BPShl, BPShr, BPSet)
  private lazy val strToPrimOp: Map[String, PrimOp] = builtinPrimOps.map { case op : PrimOp=> op.toString -> op }.toMap

  /** Seq of String representations of [[ir.PrimOp]]s */
  lazy val listing: Seq[String] = builtinPrimOps map (_.toString)
  /** Gets the corresponding [[ir.PrimOp]] from its String representation */
  def fromString(op: String): PrimOp = strToPrimOp(op)

  // Width Constraint Functions
  def PLUS (w1:Width, w2:Width) : Width = (w1, w2) match {
    case (IntWidth(i), IntWidth(j)) => IntWidth(i + j)
    case _ => PlusWidth(w1, w2)
  }
  def MAX (w1:Width, w2:Width) : Width = (w1, w2) match {
    case (IntWidth(i), IntWidth(j)) => IntWidth(Utils.max(i,j))
    case _ => MaxWidth(Seq(w1, w2))
  }
  def MINUS (w1:Width, w2:Width) : Width = (w1, w2) match {
    case (IntWidth(i), IntWidth(j)) => IntWidth(i - j)
    case _ => MinusWidth(w1, w2)
  }
  def POW (w1:Width) : Width = w1 match {
    case IntWidth(i) => IntWidth(Utils.pow_minus_one(BigInt(2), i))
    case _ => ExpWidth(w1)
  }
  def MIN (w1:Width, w2:Width) : Width = (w1, w2) match {
    case (IntWidth(i), IntWidth(j)) => IntWidth(Utils.min(i,j))
    case _ => MinWidth(Seq(w1, w2))
  }

  // Borrowed from Stanza implementation
  def set_primop_type (e:DoPrim) : DoPrim = {
    //println-all(["Inferencing primop type: " e])
    def t1 = e.args.head.tpe
    def t2 = e.args(1).tpe
    def t3 = e.args(2).tpe
    def w1 = getWidth(e.args.head.tpe)
    def w2 = getWidth(e.args(1).tpe)
    def p1 = t1 match { case FixedType(w, p) => p } //Intentional
    def p2 = t2 match { case FixedType(w, p) => p } //Intentional
    def c1 = IntWidth(e.consts.head)
    def c2 = IntWidth(e.consts(1))
    e copy (tpe = e.op match {
      case Add => (t1, t2) match {
        case (_: UIntType, _: UIntType) => UIntType(PLUS(MAX(w1, w2), IntWidth(1)))
        case (_: SIntType, _: SIntType) => SIntType(PLUS(MAX(w1, w2), IntWidth(1)))
        case (_: FixedType, _: FixedType) => FixedType(PLUS(PLUS(MAX(p1, p2), MAX(MINUS(w1, p1), MINUS(w2, p2))), IntWidth(1)), MAX(p1, p2))
        case _ => UnknownType
      }
      case Sub => (t1, t2) match {
        case (_: UIntType, _: UIntType) => UIntType(PLUS(MAX(w1, w2), IntWidth(1)))
        case (_: SIntType, _: SIntType) => SIntType(PLUS(MAX(w1, w2), IntWidth(1)))
        case (_: FixedType, _: FixedType) => FixedType(PLUS(PLUS(MAX(p1, p2),MAX(MINUS(w1, p1), MINUS(w2, p2))),IntWidth(1)), MAX(p1, p2))
        case _ => UnknownType
      }
      case Mul => (t1, t2) match {
        case (_: UIntType, _: UIntType) => UIntType(PLUS(w1, w2))
        case (_: SIntType, _: SIntType) => SIntType(PLUS(w1, w2))
        case (_: FixedType, _: FixedType) => FixedType(PLUS(w1, w2), PLUS(p1, p2))
        case _ => UnknownType
      }
      case Div => (t1, t2) match {
        case (_: UIntType, _: UIntType) => UIntType(w1)
        case (_: SIntType, _: SIntType) => SIntType(PLUS(w1, IntWidth(1)))
        case _ => UnknownType
      }
      case Rem => (t1, t2) match {
        case (_: UIntType, _: UIntType) => UIntType(MIN(w1, w2))
        case (_: SIntType, _: SIntType) => SIntType(MIN(w1, w2))
        case _ => UnknownType
      }
      case Lt => (t1, t2) match {
        case (_: UIntType, _: UIntType) => Utils.BoolType
        case (_: SIntType, _: SIntType) => Utils.BoolType
        case (_: FixedType, _: FixedType) => Utils.BoolType
        case _ => UnknownType
      }
      case Leq => (t1, t2) match {
        case (_: UIntType, _: UIntType) => Utils.BoolType
        case (_: SIntType, _: SIntType) => Utils.BoolType
        case (_: FixedType, _: FixedType) => Utils.BoolType
        case _ => UnknownType
      }
      case Gt => (t1, t2) match {
        case (_: UIntType, _: UIntType) => Utils.BoolType
        case (_: SIntType, _: SIntType) => Utils.BoolType
        case (_: FixedType, _: FixedType) => Utils.BoolType
        case _ => UnknownType
      }
      case Geq => (t1, t2) match {
        case (_: UIntType, _: UIntType) => Utils.BoolType
        case (_: SIntType, _: SIntType) => Utils.BoolType
        case (_: FixedType, _: FixedType) => Utils.BoolType
        case _ => UnknownType
      }
      case Eq => (t1, t2) match {
        case (_: UIntType, _: UIntType) => Utils.BoolType
        case (_: SIntType, _: SIntType) => Utils.BoolType
        case (_: FixedType, _: FixedType) => Utils.BoolType
        case _ => UnknownType
      }
      case Neq => (t1, t2) match {
        case (_: UIntType, _: UIntType) => Utils.BoolType
        case (_: SIntType, _: SIntType) => Utils.BoolType
        case (_: FixedType, _: FixedType) => Utils.BoolType
        case _ => UnknownType
      }
      case Pad => t1 match {
        case _: UIntType => UIntType(MAX(w1, c1))
        case _: SIntType => SIntType(MAX(w1, c1))
        case _: FixedType => FixedType(MAX(w1, c1), p1)
        case _ => UnknownType
      }
      case AsUInt => t1 match {
        case _: UIntType => UIntType(w1)
        case _: SIntType => UIntType(w1)
        case _: FixedType => UIntType(w1)
        case ClockType => UIntType(IntWidth(1))
        case AnalogType(w) => UIntType(w1)
        case _ => UnknownType
      }
      case AsSInt => t1 match {
        case _: UIntType => SIntType(w1)
        case _: SIntType => SIntType(w1)
        case _: FixedType => SIntType(w1)
        case ClockType => SIntType(IntWidth(1))
        case _: AnalogType => SIntType(w1)
        case _ => UnknownType
      }
      case AsFixedPoint => t1 match {
        case _: UIntType => FixedType(w1, c1)
        case _: SIntType => FixedType(w1, c1)
        case _: FixedType => FixedType(w1, c1)
        case ClockType => FixedType(IntWidth(1), c1)
        case _: AnalogType => FixedType(w1, c1)
        case _ => UnknownType
      }
      case AsClock => t1 match {
        case _: UIntType => ClockType
        case _: SIntType => ClockType
        case ClockType => ClockType
        case _: AnalogType => ClockType
        case _ => UnknownType
      }
      case Shl => t1 match {
        case _: UIntType => UIntType(PLUS(w1, c1))
        case _: SIntType => SIntType(PLUS(w1, c1))
        case _: FixedType => FixedType(PLUS(w1,c1), p1)
        case _ => UnknownType
      }
      case Shr => t1 match {
        case _: UIntType => UIntType(MAX(MINUS(w1, c1), IntWidth(1)))
        case _: SIntType => SIntType(MAX(MINUS(w1, c1), IntWidth(1)))
        case _: FixedType => FixedType(MAX(MAX(MINUS(w1,c1), IntWidth(1)), p1), p1)
        case _ => UnknownType
      }
      case Dshl => t1 match {
        case _: UIntType => UIntType(PLUS(w1, POW(w2)))
        case _: SIntType => SIntType(PLUS(w1, POW(w2)))
        case _: FixedType => FixedType(PLUS(w1, POW(w2)), p1)
        case _ => UnknownType
      }
      case Dshr => t1 match {
        case _: UIntType => UIntType(w1)
        case _: SIntType => SIntType(w1)
        case _: FixedType => FixedType(w1, p1)
        case _ => UnknownType
      }
      case Cvt => t1 match {
        case _: UIntType => SIntType(PLUS(w1, IntWidth(1)))
        case _: SIntType => SIntType(w1)
        case _ => UnknownType
      }
      case Neg => t1 match {
        case _: UIntType => SIntType(PLUS(w1, IntWidth(1)))
        case _: SIntType => SIntType(PLUS(w1, IntWidth(1)))
        case _ => UnknownType
      }
      case Not => t1 match {
        case _: UIntType => UIntType(w1)
        case _: SIntType => UIntType(w1)
        case _ => UnknownType
      }
      case And => (t1, t2) match {
        case (_: SIntType | _: UIntType, _: SIntType | _: UIntType) => UIntType(MAX(w1, w2))
        case _ => UnknownType
      }
      case Or => (t1, t2) match {
        case (_: SIntType | _: UIntType, _: SIntType | _: UIntType) => UIntType(MAX(w1, w2))
        case _ => UnknownType
      }
      case Xor => (t1, t2) match {
        case (_: SIntType | _: UIntType, _: SIntType | _: UIntType) => UIntType(MAX(w1, w2))
        case _ => UnknownType
      }
      case Andr => t1 match {
        case (_: UIntType | _: SIntType) => Utils.BoolType
        case _ => UnknownType
      }
      case Orr => t1 match {
        case (_: UIntType | _: SIntType) => Utils.BoolType
        case _ => UnknownType
      }
      case Xorr => t1 match {
        case (_: UIntType | _: SIntType) => Utils.BoolType
        case _ => UnknownType
      }
      case Cat => (t1, t2) match {
        case (_: UIntType | _: SIntType | _: FixedType, _: UIntType | _: SIntType | _: FixedType) => UIntType(PLUS(w1, w2))
        case (t1, t2) => UnknownType
      }
      case Bits => t1 match {
        case (_: UIntType | _: SIntType) => UIntType(PLUS(MINUS(c1, c2), IntWidth(1)))
        case _: FixedType => UIntType(PLUS(MINUS(c1, c2), IntWidth(1)))
        case _ => UnknownType
      }
      case Head => t1 match {
        case (_: UIntType | _: SIntType | _: FixedType) => UIntType(c1)
        case _ => UnknownType
      }
      case Tail => t1 match {
        case (_: UIntType | _: SIntType | _: FixedType) => UIntType(MINUS(w1, c1))
        case _ => UnknownType
      }
      case BPShl => t1 match {
        case _: FixedType => FixedType(PLUS(w1,c1), PLUS(p1, c1))
        case _ => UnknownType
      }
      case BPShr => t1 match {
        case _: FixedType => FixedType(MINUS(w1,c1), MINUS(p1, c1))
        case _ => UnknownType
      }
      case BPSet => t1 match {
        case _: FixedType => FixedType(PLUS(c1, MINUS(w1, p1)), c1)
        case _ => UnknownType
      }
    })
  }
}

/* CUSTOM NODES */

sealed trait HasDescription {
  def description: Description
}

sealed abstract class Description extends FirrtlNode

case class DocString(string: StringLit) extends Description {
  def serialize: String = "@[" + string.serialize + "]"
}

case object EmptyDescription extends Description {
  def serialize: String = ""
}

case class DescribedStmt(description: Description, stmt: Statement) extends Statement with HasDescription {
  def serialize: String = s"${description.serialize}\n${stmt.serialize}"
  def mapStmt(f: Statement => Statement): Statement = f(stmt)
  def mapExpr(f: Expression => Expression): Statement = this.copy(stmt = stmt.mapExpr(f))
  def mapType(f: Type => Type): Statement = this.copy(stmt = stmt.mapType(f))
  def mapString(f: String => String): Statement = this.copy(stmt = stmt.mapString(f))
  def mapInfo(f: Info => Info): Statement = this.copy(stmt = stmt.mapInfo(f))
}

case class DescribedMod(description: Description,
  portDescriptions: Map[String, Description],
  mod: DefModule) extends DefModule with HasDescription {
  val info = mod.info
  val name = mod.name
  val ports = mod.ports
  def serialize: String = s"${description.serialize}\n${mod.serialize}"
  def mapStmt(f: Statement => Statement): DefModule = this.copy(mod = mod.mapStmt(f))
  def mapPort(f: Port => Port): DefModule = this.copy(mod = mod.mapPort(f))
  def mapString(f: String => String): DefModule = this.copy(mod = mod.mapString(f))
  def mapInfo(f: Info => Info): DefModule = this.copy(mod = mod.mapInfo(f))
}

abstract class CustomStatement extends Statement {
  def id: String
  def stmt: Statement
  def update(newStmt: Statement): Statement

  final def mapStmt(f: Statement => Statement): Statement = update(f(stmt))
  final def mapExpr(f: Expression => Expression): Statement = this
  final def mapType(f: Type => Type): Statement = this
  final def mapString(f: String => String): Statement = this
  final def mapInfo(f: Info => Info): Statement = this
}

abstract class CustomExpression extends Expression {
  def id: String
  def expr: Expression
  def update(newExpr: Expression): Expression

  def tpe: Type
  final def mapExpr(f: Expression => Expression): Expression = update(f(expr))
  final def mapType(f: Type => Type): Expression = this
  final def mapWidth(f: Width => Width): Expression = this
}
