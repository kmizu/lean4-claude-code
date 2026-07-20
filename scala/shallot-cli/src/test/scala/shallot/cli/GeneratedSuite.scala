package shallot.cli

import shallot.gen.*

/** M1 differential gate: the expected values below mirror the Lean-side
  * `#guard` facts in `lean/Shallot/Tests/Guards.lean` — the same functions,
  * the same inputs, checked on both sides of the extraction boundary.
  * (The full JSONL corpus harness replaces this in M2.)
  */
class GeneratedSuite extends munit.FunSuite:
  test("area 6 7 = 42"):
    assertEquals(area(6, 7), BigInt(42))

  test("clampSub truncates like Lean Nat.sub"):
    assertEquals(clampSub(3, 5), BigInt(0))
    assertEquals(clampSub(5, 3), BigInt(2))

  test("shift origin 3 has x = 3"):
    assertEquals(shift(origin, 3).x, BigInt(3))
    assertEquals(shift(origin, 3).y, BigInt(0))

  test("greet appends"):
    assertEquals(greet("kouta"), "hello, kouta")

  test("divModSum matches Lean Euclidean semantics"):
    assertEquals(divModSum(-7, 2), BigInt(-3))
    assertEquals(divModSum(7, -2), BigInt(-2))
