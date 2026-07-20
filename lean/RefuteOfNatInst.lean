import Lens.Driver
import Lens.Printer

/-! Adversarial probe for the OfNat-instance finding (Translate.lean:177):
does a custom `OfNat Nat 5` instance with value 7 get silently folded to
`BigInt(5)` in extracted Scala while Lean evaluates 7? -/

open Lean Meta Lens

instance weird : OfNat Nat 5 := ⟨7⟩

def cap4 : Nat := 5

-- Lean ground truth
#eval do IO.println s!"lean cap4 = {cap4}"

-- Show the elaborated value (which instance did the literal pick up?)
set_option pp.all true in
#print cap4

#eval show MetaM Unit from do
  match ← extractModule [`cap4] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
