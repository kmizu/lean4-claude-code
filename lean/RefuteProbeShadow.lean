import Lens.Driver
import Lens.Printer
import Shallot.Demo

/-! Adversarial refutation probe: does a parameter named `fib` capture the
stripped-prefix global reference to `Shallot.fib`? -/

open Lean Meta Lens

def cap2 (fib : Nat -> Nat) : Nat := Shallot.fib 3 + fib 3

-- Lean ground truth
#eval do IO.println s!"lean cap2 (fun _ => 100) = {cap2 (fun _ => 100)}"

#eval show MetaM Unit from do
  match ← extractModule [`cap2] {} with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
