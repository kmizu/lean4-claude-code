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

end Shallot
