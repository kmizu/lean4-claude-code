import Shallot.Peg.Syntax

/-!
# Canonical result renderer

Written once in Lean, **extracted** to Scala — so the differential harness's
Lean side (running this natively) and Scala side (running the generated
version) share one rendering implementation. Renderer drift IS extractor
drift, which is exactly what the harness is meant to detect.

Corpus discipline: rendered results never contain quotes or newlines, so the
JSONL envelope needs no escaping.
-/

namespace Shallot

def renderNat (n : Nat) : String := Nat.repr n

def renderInt (i : Int) : String := Int.repr i

def renderBool (b : Bool) : String := if b = true then "true" else "false"

/-- PEG result: `fuel` / `fail` / `ok+<uncomsumed length>` (tree shape is
covered by determinism at the Lean level; the harness pins consumption). -/
def renderPeg (o : Option Outcome) : String :=
  match o with
  | none => "fuel"
  | some .fail => "fail"
  | some (.ok _ rest) => "ok+" ++ renderNat (lenChars rest)

end Shallot
