import Lens.Driver
import Lens.Printer

/-! Adversarial verification probe for the "bare global captured by local
binder" finding. Exact claimed scenario. -/

open Lean Meta Lens

namespace Shallot

def c0 : Nat := 5

def captureD (c0 : Nat) : Nat := _root_.Shallot.c0 + c0

end Shallot

-- Lean ground truth
#eval do IO.println s!"lean captureD 10 = {Shallot.captureD 10}"

#eval show MetaM Unit from do
  match ← extractModule [`Shallot.captureD] {} with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
