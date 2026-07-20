import Lens.Driver
import Lens.Printer

/-! Adversarial refutation probe: does a user parameter named `_g0` get
captured by the printer-generated literal-guard binder `_g0`? -/

open Lean Meta Lens

def capC (_g0 : Nat) : Nat -> Nat
  | 5 => _g0
  | n => n

-- Lean ground truth
#eval do IO.println s!"lean capC 42 5 = {capC 42 5}"
#eval do IO.println s!"lean capC 42 7 = {capC 42 7}"

#eval show MetaM Unit from do
  match ← extractModule [`capC] {} with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
