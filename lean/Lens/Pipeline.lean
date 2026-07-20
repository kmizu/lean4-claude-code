import Lean
import Lens.Translate
import Lens.Printer

/-!
# Extraction pipeline entry points (shared by `extract` CLI and golden tests)
-/

namespace Lens

open Lean

/-- Default extraction roots (M1 demo). Grows with each milestone. -/
def defaultRoots : List Name :=
  [`Shallot.origin, `Shallot.area, `Shallot.shift, `Shallot.clampSub,
   `Shallot.greet, `Shallot.divModSum]

/-- Load `module`'s compiled environment and run extraction to Scala text. -/
def runPipeline (module : Name) (roots : List Name) (cfg : Config) :
    IO (Except (Array LensError) String) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module }] {} (trustLevel := 0)
  let coreCtx : Core.Context := { fileName := "<lens>", fileMap := default }
  let coreState : Core.State := { env }
  let (res, _) ← (Meta.MetaM.run' (extractModule roots cfg)).toIO coreCtx coreState
  match res with
  | .ok m => return .ok (Printer.renderModule m)
  | .error errs => return .error errs

def reportErrors (errs : Array LensError) : IO Unit := do
  IO.eprintln s!"lens: extraction FAILED with {errs.size} error(s); no output written."
  for e in errs do
    IO.eprintln ("  " ++ e.render)

end Lens
