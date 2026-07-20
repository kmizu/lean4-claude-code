import Lean

/-!
# Lens CLI (M0 seed)

M0 scope: prove that a `lake exe` metaprogram can load the compiled Shallot
environment and inspect constants. The real pipeline (closure → MiniScala IR
→ pretty-printer → .scala files) lands in M1+.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Shallot }] {} (trustLevel := 0)
  let roots := args.filter (fun a => !a.startsWith "--") |>.map String.toName
  let roots := if roots.isEmpty then [`Shallot.hello, `Shallot.Color.describe] else roots
  for r in roots do
    match env.find? r with
    | some info =>
      let deps := info.getUsedConstantsAsSet
      IO.println s!"{r}: {deps.size} used constants"
    | none =>
      IO.eprintln s!"lens: unknown constant '{r}'"
      return 1
  return 0
