import Lens.Driver
import Lens.Printer

/-! Adversarial probe for the Printer.lean:113 guard-name finding:
a user parameter literally named `_g0`, referenced in a case whose
literal pattern forces the printer to synthesize guard binder `_g0`. -/

open Lean Meta Lens

def capC (_g0 : Nat) : Nat → Nat
  | 5 => _g0
  | n => n

-- Lean ground truth: first arg is returned when scrutinee = 5
#eval do IO.println s!"LEAN capC 42 5 = {capC 42 5}"
#eval do IO.println s!"LEAN capC 42 7 = {capC 42 7}"

-- Which route does the driver take?
#eval show MetaM Unit from do
  match ← getEqnsFor? `capC with
  | some eqns => IO.println s!"getEqnsFor? capC = some {eqns.toList}"
  | none => IO.println "getEqnsFor? capC = none (plain transDef route)"

-- Inspect the binder names in the signature
#eval show MetaM Unit from do
  match (← getEnv).find? `capC with
  | some (.defnInfo dv) =>
    forallTelescopeReducing dv.type fun xs _ => do
      for x in xs do
        let ld ← x.fvarId!.getDecl
        IO.println s!"sig binder: userName='{ld.userName}', hasMacroScopes={ld.userName.hasMacroScopes}"
  | _ => IO.println "no capC"

-- Run the actual extraction pipeline
#eval show MetaM Unit from do
  match ← extractModule [`capC] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
