import Lens.Driver
import Lens.Printer

/-! Adversarial re-verification of the Mangle.binderName:60 capture finding,
using the exact decls from the finding. -/

open Lean Meta Lens

def applyF (g : Nat → Nat) (n : Nat) : Nat := g n

def cap1 (x1 : Nat) : Nat := applyF (fun _ => x1) 0

-- Lean ground truth
#eval do IO.println s!"LEAN cap1 42 = {cap1 42}"

-- Inspect the elaborated body: does the inner lambda binder have macro scopes?
#eval show MetaM Unit from do
  match (← getEnv).find? `cap1 with
  | some (.defnInfo dv) =>
    IO.println s!"cap1 raw value: {dv.value}"
    let rec findLam (e : Expr) : MetaM Unit := do
      match e with
      | .lam n _ b _ =>
        IO.println s!"lambda binder: userName='{n}', hasMacroScopes={n.hasMacroScopes}, isAnonymous={n == Name.anonymous}"
        findLam b
      | .app f a => findLam f; findLam a
      | .mdata _ b => findLam b
      | .letE _ t v b _ => findLam t; findLam v; findLam b
      | _ => pure ()
    findLam dv.value
  | _ => IO.println "no cap1"

-- Which route does the driver take (equations or plain transDef)?
#eval show MetaM Unit from do
  match ← getEqnsFor? `cap1 with
  | some eqns => IO.println s!"getEqnsFor? cap1 = some {eqns.toList}"
  | none => IO.println "getEqnsFor? cap1 = none (plain transDef route)"

-- Run the actual extraction pipeline (same code path as `lake exe extract`)
#eval show MetaM Unit from do
  match ← extractModule [`cap1, `applyF] { stripPrefix := .anonymous } with
  | .ok m =>
    IO.println "=== EXTRACTION SUCCEEDED (no error) ==="
    IO.println (Printer.renderModule m)
  | .error errs =>
    IO.println "=== EXTRACTION FAILED (fail-loud) ==="
    for e in errs do IO.println ("  " ++ e.render)
