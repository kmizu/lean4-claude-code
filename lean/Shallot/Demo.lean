import Shallot.Basic

/-!
# M1 extraction demo

Match-free, non-recursive definitions exercising extractor v0:
structures, constructor application, projections, arithmetic through
`HAdd`/`HMul`/`HSub` instances, string append, literals.

Pattern matching (v2) and recursion (v1) arrive in later milestones.
-/

namespace Shallot

structure Point where
  x : Nat
  y : Nat

def origin : Point := ⟨0, 0⟩

def area (w h : Nat) : Nat := w * h

def shift (p : Point) (dx : Nat) : Point := ⟨p.x + dx, p.y⟩

/-- Goes through Lean's truncated `Nat` subtraction. -/
def clampSub (a b : Nat) : Nat := a - b

def greet (name : String) : String := "hello, " ++ name

/-- Euclidean division/modulo — Lean's default `Int` semantics (pinned M1). -/
def divModSum (a b : Int) : Int := a / b + a % b

/-! ## M2 additions: recursion through the equation route -/

/-- Structural recursion, non-tail (`@tailrec` must NOT be emitted). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Two-step `Nat.succ` patterns (`n + 2` flattens to a guard case). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Well-founded recursion, tail-recursive (`@tailrec` should be emitted). -/
def gcd (a b : Nat) : Nat :=
  if a = 0 then b else gcd (b % a) a
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by assumption))

/-- Non-recursive top-level pattern matching (also the equation route). -/
def describeColor (c : Color) : String := Color.describe c

end Shallot
