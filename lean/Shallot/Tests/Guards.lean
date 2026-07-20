import Shallot.Demo

/-!
# Semantics guards

`#guard` facts that pin primitive semantics at build time. The Scala runtime
prelude and the differential corpus assert the **same** values — any mismatch
between Lean and the extraction runtime shows up as a red test on one side.

Pinned by `#eval` (M1): Lean `Int` default `/` and `%` are **Euclidean**
(`ediv`/`emod`): remainder is always non-negative; division by zero yields 0
and `x % 0 = x`. `Nat` subtraction truncates at zero; `Nat` division by zero
yields 0 and `x % 0 = x`.
-/

namespace Shallot

-- Nat: truncated subtraction, div/mod by zero
#guard clampSub 3 5 = 0
#guard clampSub 5 3 = 2
#guard (7 : Nat) / 0 = 0
#guard (7 : Nat) % 0 = 7

-- Int: Euclidean division/modulo (default `/`, `%`)
#guard ((-7 : Int) / 2) = -4
#guard ((7 : Int) / -2) = -3
#guard ((-7 : Int) % 2) = 1
#guard ((7 : Int) % -2) = 1
#guard ((7 : Int) / 0) = 0
#guard ((-7 : Int) % 0) = -7
#guard divModSum (-7) 2 = -3

-- Demo functions
#guard area 6 7 = 42
#guard (shift origin 3).x = 3
#guard greet "kouta" = "hello, kouta"

-- Recursive demo functions (M2)
#guard fact 10 = 3628800
#guard fib 20 = 6765
#guard gcd 48 36 = 12
#guard gcd 0 5 = 5
#guard gcd 17 5 = 1
#guard describeColor .green = "green"

end Shallot
