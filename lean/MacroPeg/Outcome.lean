import MacroPeg.Interp

/-!
# Counterexample search: comparable outcomes

A flattened, string-comparable view of `MOutcome ⊕ "no answer at any
fuel bound"`, used to describe what a counterexample grammar does under a
given strategy without carrying the full `MTree`/proof machinery — this is
what gets serialized into `CounterexampleCorpus.lean`'s frozen table and
compared against the Scala reference's `EvaluationResult`.
-/

namespace Shallot.MacroPeg

/-- `accept rest`: succeeds, `rest` characters remain. `reject`: fails.
`diverge`: no outcome at any fuel bound tried (the search/reporting layer's
best-effort signal, not a machine-checked non-termination proof — that's
what `Divergence.lean`'s `selfCallDiverges` is for, when a specific
grammar/input needs a genuine proof rather than an empirical bound). -/
inductive CmpOutcome where
  | accept (rest : List Char)
  | reject
  | diverge
  deriving DecidableEq, Repr

/-- Flattens a genuine `MOutcome` (`ofMOutcome` never produces `.diverge` —
that arm exists only for the fuel-bounded search layer's own "gave up
within the tried bound" reporting). -/
def CmpOutcome.ofMOutcome : MOutcome → CmpOutcome
  | .ok _ rest => .accept rest
  | .fail => .reject

/-- Runs `mpegRun` at a fixed fuel bound and flattens the result: `none`
(ran out of fuel) is reported as `.diverge` — an empirical signal for the
search/reporting layer, not a proof of non-termination. -/
def CmpOutcome.ofRun (g : MGrammar) (s : Strategy) (fuel : Nat) (e : MExp)
    (input : List Char) : CmpOutcome :=
  match mpegRun g s fuel e input with
  | none => .diverge
  | some o => CmpOutcome.ofMOutcome o

end Shallot.MacroPeg
