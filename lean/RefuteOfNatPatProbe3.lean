import Lens.Driver
import Lens.Printer

open Lean Meta Lens

instance (priority := high) weirdP : OfNat Nat 5 := ⟨7⟩

def isFive : Nat → Bool
  | 5 => true
  | _ => false

#eval do
  IO.println s!"lean isFive over 0..9 = {(List.range 10).map isFive}"

set_option pp.all true in
#check @isFive.eq_1

#eval show MetaM Unit from do
  match ← extractModule [`isFive] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
