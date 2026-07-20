import Lens.Driver
import Lens.Printer

/-! Adversarial verification of the Translate.lean:195 finding:
custom `Div Int` instance (T-division) silently extracted as core
Euclidean `RT.intDiv`? -/

open Lean Meta Lens

instance myDiv : Div Int := ⟨Int.tdiv⟩
def cap3 : Int := (-7) / 2

-- Lean ground truth
#eval do IO.println s!"lean cap3 = {cap3}"
#eval do IO.println s!"Int.tdiv (-7) 2 = {Int.tdiv (-7) 2}"
#eval do IO.println s!"Int.ediv (-7) 2 = {Int.ediv (-7) 2}"

-- Which instance did elaboration pick?
set_option pp.explicit true in
#print cap3

#eval show MetaM Unit from do
  match ← extractModule [`cap3] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
