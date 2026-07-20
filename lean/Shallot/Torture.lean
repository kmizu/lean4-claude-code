import Shallot.Basic

/-!
# Extractor torture tests (regression suite for review findings)

Every definition here reproduced a CONFIRMED extractor bug at some point;
each stays in the differential corpus forever. Sources: the M2 TCB review
(variable-capture cluster, literal ranges).
-/

namespace Shallot

def applyF (g : Nat → Nat) (n : Nat) : Nat := g n

/-- Review #1a: the anonymous lambda binder used to be auto-named `x1`,
capturing the parameter — extracted `cap1 42` returned 0 instead of 42. -/
def cap1 (x1 : Nat) : Nat := applyF (fun _ => x1) 0

/-- Review #1b: `x'` sanitizes to `x_p`, which used to collide with the
parameter literally named `x_p` — `capB 3 5` returned 12 instead of 10. -/
def capB (x_p : Nat) : Nat → Nat
  | x' + 1 => x_p * 2 + x'
  | 0 => x_p

def c0 : Nat := 5

/-- Review #2: the parameter `c0` used to shadow the bare-printed global
`c0` — `captureD 10` returned 20 instead of 15. -/
def captureD (c0 : Nat) : Nat := Shallot.c0 + c0

/-- Review (printer): literals in `(Int.MaxValue, 2^62]` used to render as
raw Scala literals that do not compile. -/
def bigLit : Nat := 5000000000

#guard cap1 42 = 42
#guard capB 3 5 = 10
#guard captureD 10 = 15
#guard bigLit = 5000000000

end Shallot
