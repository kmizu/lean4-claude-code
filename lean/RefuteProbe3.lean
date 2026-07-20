import Lens.Driver
import Lens.Printer

/-! Adversarial probe 3: non-canonical HAdd / OfNat instances —
does the extractor reject them fail-loud, or silently emit canonical ops? -/

open Lean Meta Lens

-- Scenario 1: non-canonical HAdd instance at Nat.
instance weirdHAdd : HAdd Nat Nat Nat := ⟨fun a b => a * b⟩
def weirdAdd (a b : Nat) : Nat := a + b

#eval do IO.println s!"lean weirdAdd 2 3 = {weirdAdd 2 3}"

-- Scenario 2: non-canonical OfNat instance.
instance weirdOfNat5 : OfNat Nat 5 := ⟨7⟩
def weirdFive : Nat := (5 : Nat)

#eval do IO.println s!"lean weirdFive = {weirdFive}"

-- Show what the elaborated bodies actually look like.
#eval show MetaM Unit from do
  let some (.defnInfo dv) := (← getEnv).find? `weirdAdd | pure ()
  IO.println s!"weirdAdd body: {← Meta.ppExpr dv.value}"
  IO.println s!"weirdAdd raw: {dv.value}"
  let some (.defnInfo dv2) := (← getEnv).find? `weirdFive | pure ()
  IO.println s!"weirdFive body: {← Meta.ppExpr dv2.value}"
  IO.println s!"weirdFive raw: {dv2.value}"

#eval show MetaM Unit from do
  match ← extractModule [`weirdAdd, `weirdFive] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
