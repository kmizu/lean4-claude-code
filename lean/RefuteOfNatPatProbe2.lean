import Lens.Driver
import Lens.Printer

open Lean Meta Lens

instance weirdP : OfNat Nat 5 := ⟨7⟩

def isFive : Nat → Bool
  | 5 => true
  | _ => false

-- decisive: apply to raw values 0..9 built without any OfNat literal
#eval do
  IO.println s!"lean isFive over 0..9 = {(List.range 10).map isFive}"

#eval show MetaM Unit from do
  match ← getEqnsFor? ``isFive with
  | some eqns =>
    for eq in eqns do
      if let some ci := (← getEnv).find? eq then
        IO.println s!"eqn {eq}: {← Meta.ppExpr ci.type}"
  | none => IO.println "no eqns"
