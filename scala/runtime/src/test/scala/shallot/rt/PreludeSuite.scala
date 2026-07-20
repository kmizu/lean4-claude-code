package shallot.rt

class PreludeSuite extends munit.FunSuite:
  test("natSub truncates at zero (Lean semantics)"):
    assertEquals(Prelude.natSub(3, 5), BigInt(0))
    assertEquals(Prelude.natSub(5, 3), BigInt(2))
    assertEquals(Prelude.natSub(0, 0), BigInt(0))

  test("nat div/mod by zero follow Lean semantics"):
    assertEquals(Prelude.natDiv(7, 0), BigInt(0))
    assertEquals(Prelude.natMod(7, 0), BigInt(7))
    assertEquals(Prelude.natDiv(7, 2), BigInt(3))
    assertEquals(Prelude.natMod(7, 2), BigInt(1))

  test("panic throws LensPanic"):
    intercept[Prelude.LensPanic] {
      Prelude.panic[Int]("boom")
    }

  test("Stack.run executes deep recursion on a big stack"):
    def deep(n: Int): Int = if n == 0 then 0 else 1 + deep(n - 1)
    assertEquals(Stack.run(64)(deep(200_000)), 200_000)
