import Lens.Driver
import Lens.Printer

/-! Adversarial probe 5: non-canonical HAdd/OfNat instances — does the
extractor accept them and silently emit the canonical Scala operation? -/

open Lean Meta Lens

instance weirdHAddInst : HAdd Nat Nat Nat := ⟨fun a b => a * b⟩
def weirdAdd (a b : Nat) : Nat := a + b

instance weirdOfNatInst : OfNat Nat 5 := ⟨7⟩
def weirdFive : Nat := (5 : Nat)

-- Lean ground truth
#eval do IO.println s!"lean weirdAdd 2 3 = {weirdAdd 2 3}"
#eval do IO.println s!"lean weirdFive = {weirdFive}"

-- Which instance did elaboration pick?
set_option pp.explicit true in
#print weirdAdd
set_option pp.explicit true in
#print weirdFive

#eval show MetaM Unit from do
  match ← extractModule [`weirdAdd, `weirdFive] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
