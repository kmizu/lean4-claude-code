import Lens.Driver
import Lens.Printer

/-! Adversarial probe: exact scenario from the capture finding.
User param literally named `x1`, anonymous lambda binder inside the body. -/

open Lean Meta Lens

def applyF (g : Nat → Nat) (n : Nat) : Nat := g n

def cap1 (x1 : Nat) : Nat := applyF (fun _ => x1) 0

-- Lean ground truth: (fun _ => x1) 0 = x1 = 42
#eval do IO.println s!"lean cap1 42 = {cap1 42}"

#eval show MetaM Unit from do
  match ← extractModule [`cap1, `applyF] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
