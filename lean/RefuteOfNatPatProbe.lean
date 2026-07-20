import Lens.Driver
import Lens.Printer

/-! Pattern-position probe: does a literal match pattern under a custom
`OfNat Nat 5` instance extract as a guard against the numeral 5 while
Lean matches on the instance's value? -/

open Lean Meta Lens

instance weirdP : OfNat Nat 5 := ⟨7⟩

def isFive : Nat → Bool
  | 5 => true
  | _ => false

#eval do
  IO.println s!"lean isFive 5 = {isFive 5}"
  IO.println s!"lean isFive 7 = {isFive 7}"

set_option pp.all true in
#print isFive

#eval show MetaM Unit from do
  match ← getEqnsFor? ``isFive with
  | some eqns =>
    for eq in eqns do
      let some ci := (← getEnv).find? eq | continue
      IO.println s!"eqn {eq}: {← Meta.ppExpr ci.type!}"
  | none => IO.println "no eqns"

#eval show MetaM Unit from do
  match ← extractModule [`isFive] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
