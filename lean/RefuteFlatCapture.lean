import Lens.Driver
import Lens.Printer

/-! Adversarial re-verification of the Printer.lean:142 flat-global-capture
finding, using the exact decls from the finding. -/

namespace Shallot
def c0 : Nat := 5
def captureD (c0 : Nat) : Nat := _root_.Shallot.c0 + c0
end Shallot

open Lean Meta Lens

-- Lean ground truth
#eval do IO.println s!"LEAN captureD 10 = {Shallot.captureD 10}"

-- Which route does the driver take?
#eval show MetaM Unit from do
  match ← getEqnsFor? `Shallot.captureD with
  | some eqns => IO.println s!"getEqnsFor? = some {eqns.toList}"
  | none => IO.println "getEqnsFor? = none (plain transDef route)"

-- Run the actual extraction pipeline with the DEFAULT config
-- (stripPrefix := `Shallot, pkg := "shallot.gen")
#eval show MetaM Unit from do
  match ← extractModule [`Shallot.captureD] {} with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
