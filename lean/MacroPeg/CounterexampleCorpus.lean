import MacroPeg.Counterexamples
import MacroPeg.Render

/-!
# Counterexample differential corpus (single source of truth)

Mirrors `Corpus.lean`'s design: defined once, extracted for the Scala
differential harness. Each case pairs an id with the canonical
`renderMPeg` rendering of a fuel-bounded `mpegRun` — `"fail"`/`"ok+N"` for
CE-001's three strategies (all terminate quickly), `"fuel"` for CE-002
(genuinely never terminates — `Divergence.lean`'s `selfCallDiverges`
proves no fuel bound would ever produce an answer, so `"fuel"` here is not
"ran out, might succeed with more" but a witnessed, permanent fact).

CE-003 (the `MacroExpander` capture bug) has no entry here — it isn't
representable in `MExp` at all (see `Counterexamples.lean`'s module
docstring); it is independently verified in Scala only.
-/

namespace Shallot.MacroPeg

/-- CE-001 under `.callByName`: `"ab"` fails (`ce001_callByName`). -/
def ceCase001Name (id : String) : String × String :=
  (id, renderMPeg (mpegRun strategyDivergeGrammar .callByName 10
    (.call 0 []) strategyDivergeInput))

/-- CE-001 under `.callByValueSeq`: `"ab"` succeeds, fully consumed
(`ce001_callByValueSeq`). -/
def ceCase001Seq (id : String) : String × String :=
  (id, renderMPeg (mpegRun strategyDivergeGrammar .callByValueSeq 10
    (.call 0 []) strategyDivergeInput))

/-- CE-001 under `.callByValuePar`: `"ab"` fails, same as `.callByName`
(`ce001_callByValuePar`). -/
def ceCase001Par (id : String) : String × String :=
  (id, renderMPeg (mpegRun strategyDivergeGrammar .callByValuePar 10
    (.call 0 []) strategyDivergeInput))

/-- CE-002: `S`'s call never produces an answer at any fuel bound
(`selfCall_loop_none`) — `renderMPeg none = "fuel"` here reports a
PROVEN permanent fact, not an empirical "ran out." -/
def ceCase002 (id : String) : String × String :=
  (id, renderMPeg (mpegRun selfCallGrammar .callByName 10 (.call 0 []) []))

/-- The counterexample corpus: id ↦ canonical rendering. -/
def ceCases : List (String × String) :=
  [ ceCase001Name "500-ce001-strategy-name-ab",
    ceCase001Seq "501-ce001-strategy-seq-ab",
    ceCase001Par "502-ce001-strategy-par-ab",
    ceCase002 "510-ce002-selfcall-diverges" ]

end Shallot.MacroPeg
