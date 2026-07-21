import MacroPeg.Syntax
import Shallot.Render

/-!
# Macro PEG canonical result renderer

Mirrors `Shallot.renderPeg`: written once in Lean, extracted to Scala, so
the differential harness's Lean side (running this natively) and Scala side
(running the generated version) share one rendering implementation.
-/

namespace Shallot.MacroPeg

/-- Macro PEG result: `fuel` / `fail` / `ok+<unconsumed length>` (tree shape
is covered by `mderives_det`/T2 at the Lean level; the harness pins
consumption only, exactly like `renderPeg`). -/
def renderMPeg (o : Option MOutcome) : String :=
  match o with
  | none => "fuel"
  | some .fail => "fail"
  | some (.ok _ rest) => "ok+" ++ Shallot.renderNat (lenChars rest)

end Shallot.MacroPeg
