package firrtl.fuzzer

import firrtl.ir._
import firrtl.passes.CheckWidths
import firrtl.{Namespace, PrimOps, Utils}

trait Context[Gen[_]] {
  def unboundRefs: Set[Reference] // should have type set
  def decls: Set[IsDeclaration]
  def maxDepth: Int
  def withRef(ref: Reference): Context[Gen]
  def decrementDepth: Context[Gen]
  def namespace: Namespace
  def exprGen(tpe: Type): Gen[(Context[Gen], Expression)]
}

case class ExprContext(
  unboundRefs: Set[Reference],
  decls: Set[IsDeclaration],
  maxDepth: Int,
  namespace: Namespace) extends Context[ASTGen] {
  def withRef(ref: Reference): ExprContext = this.copy(unboundRefs = unboundRefs + ref)
  def decrementDepth: ExprContext = this.copy(maxDepth = maxDepth - 1)
  def exprGen(tpe: Type): ASTGen[(Context[ASTGen], Expression)] = ???
}

object Fuzzers {
  import GenMonad.implicits._
  import GenMonad.syntax._

  def intWidth[G[_]: GenMonad]: G[IntWidth] =
    GenMonad[G].choose(0, CheckWidths.MaxWidth).map(w => IntWidth(BigInt(w)))

  def intOrUnknownWidth[G[_]: GenMonad]: G[Width] =
    GenMonad[G].oneOf(
      intWidth.widen[Width],
      GenMonad[G].const(UnknownWidth).widen[Width]
    ).flatten

  def uintLit[G[_]: GenMonad]: G[UIntLiteral] = for {
    value <- GenMonad[G].choose(0, Int.MaxValue)
    width <- intOrUnknownWidth
  } yield {
    UIntLiteral(value, width)
  }

  def sintLit[G[_]: GenMonad]: G[SIntLiteral] = for {
    value <- GenMonad[G].choose(Int.MinValue, Int.MaxValue)
    width <- intOrUnknownWidth
  } yield {
    SIntLiteral(value, width)
  }

  def binaryPrimOp[G[_]: GenMonad]: G[PrimOp] = {
    import PrimOps._
    GenMonad[G].oneOf(
      Add, Sub, Mul, Div, Rem, Lt, Leq, Gt, Geq,
      Eq, Neq, /*Dshl, Dshr,*/ And, Or, Xor, Cat,
      //Clip, Wrap, Squeeze
    )
  }

  def widthOp(width: Width)(op: BigInt => BigInt): Width = width match {
    case IntWidth(i) => IntWidth(op(i))
    case UnknownWidth => UnknownWidth
  }

  def makeBinPrimOpGen[G[_]: GenMonad](
    primOp: PrimOp,
    typeFn: Type => G[(Type, Type)],
    tpe: Type)(ctx0: Context[G]): G[(Context[G], Expression)] = {
    for {
      (tpe1, tpe2) <- typeFn(tpe)
      (ctx1, expr1) <- ctx0.exprGen(tpe1)
      (ctx2, expr2) <- ctx1.exprGen(tpe2)
    } yield {
      ctx2 -> DoPrim(primOp, Seq(expr1, expr2), Seq.empty, tpe)
    }
  }

  def genAddPrimOp[G[_]: GenMonad](tpe: Type): Context[G] => G[(Context[G], Expression)] = {
    def typeFn(tpe: Type): G[(Type, Type)] = tpe match {
      case UIntType(width) =>
        val tpe = UIntType(widthOp(width)(_ - 1))
        GenMonad[G].const(tpe -> tpe)
      case SIntType(width) =>
        val tpe = UIntType(widthOp(width)(_ - 1))
        GenMonad[G].const(tpe -> tpe)
    }
    makeBinPrimOpGen(
      PrimOps.Add, typeFn, tpe)
  }
/*
  def genSubPrimOp[G[_]: GenMonad](tpe: Type): Context[G] => G[(Context[G], Expression)] = {
    val typeFn = (_: Type) match {
      case UIntType(width) => UIntType(widthOp(width)(_ - 1))
      case SIntType(width) => UIntType(widthOp(width)(_ - 1))
    }
    makeBinPrimOpGen(
      PrimOps.Add, typeFn, typeFn, tpe)
  }*/

  def binDoPrim[G[_]: GenMonad](ctx0: Context[G]): G[(Context[G], Expression)] = {
    for {
      op <- binaryPrimOp
      (ctx1, expr1) <- genExpr(ctx0)
      (ctx2, expr2) <- genExpr(ctx1)
    } yield {
      ctx2 -> PrimOps.set_primop_type(
        DoPrim(op, Seq(expr1, expr2), Seq.empty, UnknownType))
    }
  }

  def ref[G[_]: GenMonad](ctx0: Context[G], nameOpt: Option[String] = None): G[(Context[G], Reference)] = for {
    width <- GenMonad[G].choose(0, CheckWidths.MaxWidth)
    tpe <- GenMonad[G].oneOf(
      SIntType(IntWidth(BigInt(width))),
      UIntType(IntWidth(BigInt(width)))
    )
    name <- nameOpt.map(GenMonad[G].const).getOrElse(GenMonad[G].identifier(20))
  } yield {
    val ref = Reference(ctx0.namespace.newName(name), tpe)
    ctx0.withRef(ref) -> ref
  }

  def leaf[G[_]: GenMonad](ctx0: Context[G]): G[(Context[G], Expression)] = {
    GenMonad[G].oneOf(
      uintLit.map((e: Expression) => ctx0 -> e),
      sintLit.map((e: Expression) => ctx0 -> e),
      ref(ctx0).widen[(Context[G], Expression)]
    ).flatten
  }

  def genExpr[G[_]: GenMonad](ctx0: Context[G]): G[(Context[G], Expression)] = {
    if (ctx0.maxDepth <= 0) {
      leaf(ctx0)
    } else {
      GenMonad[G].oneOf(
        binDoPrim(ctx0.decrementDepth),
        leaf(ctx0),
      ).flatten
    }
  }


  def exprMod[G[_]: GenMonad](ctx0: Context[G]): G[(Context[G], Module)] = {
    for {
      (ctx1, expr) <- genExpr(ctx0)
      (ctx2, outputPortRef) <- ref(ctx1, Some("outputPort"))
    } yield {
      val outputPort = Port(
        NoInfo,
        outputPortRef.name,
        Output,
        outputPortRef.tpe
      )
      ctx1 -> Module(
        NoInfo,
        "foo",
        ctx1.unboundRefs.map { ref =>
          Port(NoInfo, ref.name, Input, ref.tpe)
        }.toSeq.sortBy(_.name) :+ outputPort,
        Connect(NoInfo, outputPortRef, expr)
      )
    }
  }

  def exprCircuit[G[_]: GenMonad](ctx: Context[G]): G[Circuit] = {
    exprMod(ctx).map { case (_, m) =>
      Circuit(NoInfo, Seq(m), m.name)
    }
  }
}

/*
  def subField(
    expr: Gen[Expression],
    name: Gen[String]
  ): Gen[SubField] = for {
    e <- expr
    n <- name
  } yield {
    SubField(e, n)
  }

  def subIndex(
    expr: Gen[Expression],
    value: Gen[Int],
  ): Gen[SubIndex] = for {
    e <- expr
    v <- value
  } yield {
    SubIndex(e, v, UnknownType)
  }

  def mux(
    cond: Gen[Expression],
    tval: Gen[Expression],
    fval: Gen[Expression]
  ): Gen[Mux] = for {
    c <- cond
    t <- tval
    f <- fval
  } yield {
    Mux(c, t, f, UnknownType)
  }

  def validIf(
    cond: Gen[Expression],
    value: Gen[Expression]
  ): Gen[ValidIf] = for {
    c <- cond
    v <- value
  } yield {
    ValidIf(c, v, UnknownType)
  }

  def groundType(gen: Gen[Expression]): Gen[Expression] = {
    gen.flatMap { expr =>
      expr.tpe match {
        case _: GroundType => Gen.const(expr)
        case BundleType(fields) =>
          groundType(Gen.oneOf(fields).map { f =>
            SubField(expr, f.name, f.tpe)
          })
        case VectorType(tpe, size) =>
          groundType(Gen.choose(0, size - 1).map { i =>
            SubIndex(expr, i, tpe)
          })
      }
    }
  }

  // def boolType(exprs: Gen[Expression]*): Gen[PrimOp] = {
  //   for {
  //     exprs
  //   }
  // }

  def binaryDoPrim(exprs: Gen[Expression]*): Gen[DoPrim] = {
    for {
      op <- binaryPrimOp
      expr1 <- Gen.oneOf(exprs).flatMap(groundType)
      expr2 <- Gen.oneOf(exprs).flatMap(groundType)
    } yield {
      PrimOps.set_primop_type(
        DoPrim(PrimOps.Add, Seq(expr1, expr2), Seq.empty, UnknownType))
    }
  }

  sealed trait TypeConstraint
  case object AnyType extends TypeConstraint
  case class Equals(tpe: Type) extends TypeConstraint
  case class ContainsField(field: String) extends TypeConstraint
  case class ContainsIndex(tpe: Type) extends TypeConstraint

  def anyExprGen(ctx: Context): ASTGen[Expression] = ???

  def mux(ctx0: Context): ASTGen[Mux] = {
    for {
      (ctx1, cond) <- exprGenWithType(ctx0, UIntType(IntWidth(1)))
      (ctx2, tval) <- anyExprGen(ctx1)
      (ctx3, fval) <- exprGenWithType(ctx2, tval.tpe)
    } yield {
      ctx3 -> Mux(cond, tval, fval)
    }
  }

  def getType(op: PrimOp, t1: Type, t2: Type): Type = {
    op match {
      case (UIntType, UIntType) =>
    }
  }

  def exprGenWithType(ctx: Context, tpe: Type): ASTGen[Expression] = {
    tpe match {
      case UIntType(UnknownWidth) =>
        doPrim()
      case UIntType(IntWidth(width)) =>
      case SIntType(UnknownWidth) =>
      case SIntType(IntWidth(width)) =>
      case FixedType =>
      case IntervalType =>
      case ClockType =>
      case ResetType =>
      case AsyncResetType =>
      case AnalogType =>
    }
  }

  def exprGenWithType(ctx: Context, tpe: Type): ASTGen[Expression] = ???

  def groundTypeBinaryDoPrim(ctx0: Context, op: PrimOp, isSigned: Boolean): ASTGen[DoPrim] = {
    val tpe = if (isSigned) SIntType(UnknownWidth) else UIntType(UnknownWidth)
    for {
      (ctx1, expr1) <- exprGenWithType(ctx0, tpe)
      (ctx2, expr2) <- exprGenWithType(ctx1, tpe)
    } yield {
      ctx2 -> PrimOps.set_primop_type(
        DoPrim(op, Seq(expr1, expr2), Seq.empty, UnknownType))
    }
  }
*/
