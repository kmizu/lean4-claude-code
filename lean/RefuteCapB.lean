import Lens.Driver
import Lens.Printer

open Lean Meta Lens

def capB (x_p : Nat) : Nat -> Nat
  | x' + 1 => x_p * 2 + x'
  | 0 => x_p

#eval do IO.println s!"lean capB 3 5 = {capB 3 5}"

#eval show MetaM Unit from do
  match ← extractModule [`capB] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED ==="
    for e in errs do IO.println ("  " ++ e.render)
