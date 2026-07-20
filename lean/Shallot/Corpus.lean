import Shallot.Demo
import Shallot.Render

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
    ("013-bool-false",        renderBool false) ]

end Shallot
