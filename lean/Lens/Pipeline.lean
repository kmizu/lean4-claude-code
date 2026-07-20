import Lean
import Lens.Driver
import Lens.Printer

/-!
# Extraction pipeline entry points (shared by `extract` CLI and golden tests)
-/

namespace Lens

open Lean

/-- Default extraction roots. Grows with each milestone. -/
def defaultRoots : List Name :=
  [`Shallot.origin, `Shallot.area, `Shallot.shift, `Shallot.clampSub,
   `Shallot.greet, `Shallot.divModSum,
   -- M2: recursion via the equation route + shared renderer
   `Shallot.fact, `Shallot.fib, `Shallot.gcd, `Shallot.describeColor,
   `Shallot.renderNat, `Shallot.renderInt, `Shallot.renderBool,
   -- M2: single-source differential case table
   `Shallot.cases]

unsafe def enableInitsUnsafe : IO Unit := enableInitializersExecution

/-- Safe wrapper: initializer execution must be enabled before
`importModules (loadExts := true)`. -/
@[implemented_by enableInitsUnsafe]
def enableInits : IO Unit := pure ()

/-- Load `module`'s compiled environment and run extraction to Scala text. -/
def runPipeline (module : Name) (roots : List Name) (cfg : Config) :
    IO (Except (Array LensError) String) := do
  initSearchPath (← findSysroot)
  enableInits
  -- v4.32.0: `loadExts` defaults to FALSE — without it, env extensions
  -- (MatcherInfo, EqnInfo, …) are missing and equation generation fails
  -- with "no progress at goal". `importAll` reads the private olean level
  -- so non-exposed extension entries are present too.
  let env ← importModules #[{ module, importAll := true }] {} (trustLevel := 0) (loadExts := true)
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
