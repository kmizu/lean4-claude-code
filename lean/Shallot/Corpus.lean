import Shallot.Demo
import Shallot.Render
import Shallot.Torture
import Shallot.Peg.Interp
import Shallot.Lang.TypeCheck
import Shallot.Lang.Eval
import Shallot.Opt.ConstFold
import Shallot.Data.RBMap

/-!
# Differential corpus (single source of truth)

The case table is defined ONCE here and **extracted**: the Lean runner
(`shallot-runner`) evaluates it natively, the Scala CLI (`dump`) evaluates
the generated version — same table, two evaluators. Any divergence is
extractor/runtime drift.

Discipline: ids and results must never contain `"` or newlines, so the
JSONL envelope needs no escaping.
-/

namespace Shallot

/-- Toy grammar: rule 0 = `[0-9]+ !.` (digits then EOF). -/
def digitGrammar : Grammar :=
  { rules := [.seq (PExp.plus (.range '0' '9')) (.notP .any)], start := 0 }

/-- Toy grammar: rule 0 = `"if" ![a-z]` (keyword with guard). -/
def kwIfGrammar : Grammar :=
  { rules := [.seq (.lit "if".toList) (.notP (.range 'a' 'z'))], start := 0 }

/-- Sample: `def fact(n: int): int = if n <= 0 then 1 else n * fact(n - 1)`
with `main = fact(5)` (as an AST — concrete syntax lands in M11). -/
def factProg : Program :=
  { funs := [
      { name := "fact", params := [("n", .int)], retTy := .int,
        body := .ite (.binop .le (.var "n") (.intLit 0))
          (.intLit 1)
          (.binop .mul (.var "n")
            (.call "fact" (.cons (.binop .sub (.var "n") (.intLit 1)) .nil))) } ],
    main := .call "fact" (.cons (.intLit 5) .nil) }

/-- Mutual recursion: even/odd. -/
def evenOddProg : Program :=
  { funs := [
      { name := "even", params := [("n", .int)], retTy := .bool,
        body := .ite (.binop .eqI (.var "n") (.intLit 0))
          (.boolLit true)
          (.call "odd" (.cons (.binop .sub (.var "n") (.intLit 1)) .nil)) },
      { name := "odd", params := [("n", .int)], retTy := .bool,
        body := .ite (.binop .eqI (.var "n") (.intLit 0))
          (.boolLit false)
          (.call "even" (.cons (.binop .sub (.var "n") (.intLit 1)) .nil)) } ],
    main := .call "even" (.cons (.intLit 10) .nil) }

/-- Reject: unbound variable in main. -/
def badUnbound : Program := { funs := [], main := .var "ghost" }

/-- Reject: `1 + true`. -/
def badMismatch : Program :=
  { funs := [], main := .binop .add (.intLit 1) (.boolLit true) }

/-- Reject: unknown function. -/
def badUnknownFun : Program :=
  { funs := [], main := .call "nope" .nil }

/-- Reject: arity mismatch. -/
def badArity : Program :=
  { funs := [
      { name := "id1", params := [("x", .int)], retTy := .int, body := .var "x" } ],
    main := .call "id1" .nil }

/-- Deep recursion: `sum(n) = if n <= 0 then 0 else n + sum(n-1)` — fuel and
stack stress (corpus 07x runs it at 20000 on both sides). -/
def sumProg (n : Int) : Program :=
  { funs := [
      { name := "sum", params := [("n", .int)], retTy := .int,
        body := .ite (.binop .le (.var "n") (.intLit 0))
          (.intLit 0)
          (.binop .add (.var "n")
            (.call "sum" (.cons (.binop .sub (.var "n") (.intLit 1)) .nil))) } ],
    main := .call "sum" (.cons (.intLit n) .nil) }

/-- Division-by-zero must surface as `divByZero`, not a stuck error. -/
def divZeroProg : Program :=
  { funs := [], main := .binop .div (.intLit 7) (.intLit 0) }

/-- Foldable expression: `(2 + 3) * (10 - 4)` under an if with known cond. -/
def foldyProg : Program :=
  { funs := [],
    main := .ite (.binop .lt (.intLit 1) (.intLit 2))
      (.binop .mul (.binop .add (.intLit 2) (.intLit 3))
                   (.binop .sub (.intLit 10) (.intLit 4)))
      (.binop .div (.intLit 1) (.intLit 0)) }

/-- RBMap smoke sequence: fromList + find hits and misses. -/
def rbDemo : String :=
  let t := RBNode.fromList [("b", 2), ("a", 1), ("c", 3), ("a", 10)]
  match RBNode.find? t "a", RBNode.find? t "c", RBNode.find? t "zz" with
  | some a, some c', none => renderNat a ++ "," ++ renderNat c' ++ ",miss"
  | _, _, _ => "unexpected"

def cases : List (String × String) :=
  [ ("000-nat-sub-underflow", renderNat (clampSub 3 5)),
    ("001-nat-sub-normal",    renderNat (clampSub 5 3)),
    ("002-int-ediv-neg",      renderInt (divModSum (-7) 2)),
    ("003-int-ediv-negdiv",   renderInt (divModSum 7 (-2))),
    ("004-bigint-fact25",     renderNat (fact 25)),
    ("005-fact-10",           renderNat (fact 10)),
    ("006-fib-20",            renderNat (fib 20)),
    ("007-gcd",               renderNat (gcd 48 36)),
    ("008-gcd-zero",          renderNat (gcd 0 5)),
    ("009-color",             describeColor .green),
    ("010-greet",             greet "corpus"),
    ("011-shift-proj",        renderNat (shift origin 3).x),
    ("012-bool-true",         renderBool true),
    ("013-bool-false",        renderBool false),
    -- Torture: confirmed extractor bugs, kept in the corpus forever
    ("100-capture-lambda",    renderNat (cap1 42)),
    ("101-capture-sanitize",  renderNat (capB 3 5)),
    ("102-capture-global",    renderNat (captureD 10)),
    ("103-large-literal",     renderNat bigLit),
    -- 01x: PEG interpreter through extraction
    ("200-peg-digits-ok",     renderPeg (pegRun digitGrammar 100 (.nt 0) "123".toList)),
    ("201-peg-digits-trail",  renderPeg (pegRun digitGrammar 100 (.nt 0) "12a".toList)),
    ("202-peg-digits-empty",  renderPeg (pegRun digitGrammar 100 (.nt 0) "".toList)),
    ("203-peg-missing-nt",    renderPeg (pegRun digitGrammar 100 (.nt 9) "1".toList)),
    ("204-peg-kw-ok",         renderPeg (pegRun kwIfGrammar 100 (.nt 0) "if x".toList)),
    ("205-peg-kw-guard",      renderPeg (pegRun kwIfGrammar 100 (.nt 0) "iffy".toList)),
    ("206-peg-not-compose",   renderPeg (pegRun kwIfGrammar 100 (.notP (.nt 0)) "iffy".toList)),
    ("207-peg-fuel-out",      renderPeg (pegRun digitGrammar 0 (.nt 0) "1".toList)),
    ("208-peg-star-empty",    renderPeg (pegRun digitGrammar 100 (.star (.range '0' '9')) "abc".toList)),
    ("209-peg-opt",           renderPeg (pegRun digitGrammar 100 (PExp.opt (.chr 'x')) "abc".toList)),
    -- 02x: RBMap through extraction
    ("300-rbmap-find",        rbDemo),
    -- 03x/04x: typechecker accept/reject
    ("310-tc-fact",           renderTC (checkProgram factProg)),
    ("311-tc-evenodd",        renderTC (checkProgram evenOddProg)),
    ("320-tc-unbound",        renderTC (checkProgram badUnbound)),
    ("321-tc-mismatch",       renderTC (checkProgram badMismatch)),
    ("322-tc-unknown",        renderTC (checkProgram badUnknownFun)),
    ("323-tc-arity",          renderTC (checkProgram badArity)),
    -- 05x: interpreter through extraction
    ("400-eval-fact",         renderEval (runProgram factProg 1000)),
    ("401-eval-evenodd",      renderEval (runProgram evenOddProg 1000)),
    ("402-eval-divzero",      renderEval (runProgram divZeroProg 1000)),
    ("403-eval-unbound",      renderEval (runProgram badUnbound 1000)),
    ("404-eval-fuel",         renderEval (runProgram (sumProg 100) 3)),
    -- 06x-prep: optimizer agreement (semantic preservation checked by diff)
    ("410-opt-foldy-direct",  renderEval (runProgram foldyProg 1000)),
    ("411-opt-foldy-opt",     renderEval (runProgram (optProgram foldyProg) 1000)),
    ("412-opt-fact-opt",      renderEval (runProgram (optProgram factProg) 1000)),
    -- 07x: deep recursion (stack stress on the Scala side)
    ("420-eval-sum-20000",    renderEval (runProgram (sumProg 20000) 100000)) ]

end Shallot
