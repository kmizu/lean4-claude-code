package shallot.cli

import munit.ScalaCheckSuite
import org.scalacheck.{Gen, Prop}
import shallot.gen.*

/** Property layer over the EXTRACTED code: the optimizer-preservation and
  * type-preservation theorems are proven in Lean (M8); these re-check the
  * same equations empirically post-extraction on random closed expressions.
  */
class OptPropertySuite extends ScalaCheckSuite:

  private def lit(n: Int): Expr = Expr.intLit(BigInt(n))

  private def intExpr(depth: Int): Gen[Expr] =
    if depth == 0 then Gen.choose(-50, 50).map(lit)
    else
      Gen.frequency(
        2 -> Gen.choose(-50, 50).map(lit),
        3 -> (for
          op <- Gen.oneOf(BinOp.add(), BinOp.sub(), BinOp.mul(), BinOp.div(), BinOp.mod())
          l <- intExpr(depth - 1)
          r <- intExpr(depth - 1)
        yield Expr.binop(op, l, r)),
        1 -> (for
          c <- boolExpr(depth - 1)
          t <- intExpr(depth - 1)
          e <- intExpr(depth - 1)
        yield Expr.ite(c, t, e))
      )

  private def boolExpr(depth: Int): Gen[Expr] =
    if depth == 0 then Gen.oneOf(Expr.boolLit(true), Expr.boolLit(false))
    else
      Gen.frequency(
        2 -> Gen.oneOf(Expr.boolLit(true), Expr.boolLit(false)),
        2 -> (for
          op <- Gen.oneOf(BinOp.lt(), BinOp.le(), BinOp.eqI())
          l <- intExpr(depth - 1)
          r <- intExpr(depth - 1)
        yield Expr.binop(op, l, r)),
        1 -> (for
          op <- Gen.oneOf(BinOp.andB(), BinOp.orB(), BinOp.eqB())
          l <- boolExpr(depth - 1)
          r <- boolExpr(depth - 1)
        yield Expr.binop(op, l, r))
      )

  private def prog(main: Expr): Program = Program(Nil, main)

  property("constant folding preserves evaluation (incl. divByZero)"):
    Prop.forAll(intExpr(4)) { e =>
      renderEval(runProgram(prog(e), BigInt(10000))) ==
        renderEval(runProgram(optProgram(prog(e)), BigInt(10000)))
    }

  property("constant folding preserves typing"):
    Prop.forAll(intExpr(4)) { e =>
      renderTC(checkProgram(prog(e))) ==
        renderTC(checkProgram(optProgram(prog(e))))
    }

  property("well-typed closed int expressions never get stuck"):
    Prop.forAll(intExpr(4)) { e =>
      renderEval(runProgram(prog(e), BigInt(10000))) match
        case s if s.startsWith("ok:") => true
        case "err:DivByZero"          => true
        case _                        => false
    }
