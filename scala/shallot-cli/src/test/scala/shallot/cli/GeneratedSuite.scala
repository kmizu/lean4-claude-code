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

  test("fact (structural recursion, non-tail)"):
    assertEquals(fact(10), BigInt(3628800))
    assertEquals(fact(0), BigInt(1))

  test("fib (two-step Nat.succ patterns)"):
    assertEquals(fib(20), BigInt(6765))
    assertEquals(fib(0), BigInt(0))
    assertEquals(fib(1), BigInt(1))

  test("gcd (well-founded recursion, @tailrec emitted)"):
    assertEquals(gcd(48, 36), BigInt(12))
    assertEquals(gcd(0, 5), BigInt(5))
    assertEquals(gcd(17, 5), BigInt(1))

  test("describeColor (ADT pattern match via equations)"):
    assertEquals(describeColor(Color.green()), "green")
    assertEquals(describeColor(Color.red()), "red")

  test("shared renderer"):
    assertEquals(renderNat(42), "42")
    assertEquals(renderInt(-7), "-7")
    assertEquals(renderBool(true), "true")
    assertEquals(renderBool(false), "false")
