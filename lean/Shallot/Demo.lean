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

end Shallot
