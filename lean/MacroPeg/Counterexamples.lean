import MacroPeg.Outcome
import MacroPeg.Divergence

/-!
# Counterexample corpus: CE-001, CE-002, CE-003

Three witnesses that the reference `Evaluator`'s three strategies, and its
`GrammarValidator`/`MacroExpander` utilities, do NOT all agree with each
other — each grounded against the LIVE reference implementation
(`/home/mizushima/repo/macro_peg`, commit `528e964`) during this session,
not assumed from an earlier planning pass (an earlier draft of this plan
had CE-001's expected outputs WRONG — re-verifying against the actual
`sbt console` output caught this before it was formalized as a false
claim).

- **CE-001** (evaluation-strategy non-equivalence): formalized here, all
  three strategies machine-checked by unfolding the fuel-indexed
  interpreter (`mpegRun`) via `simp` — the cheapest possible evidence for
  a claim about a small, concrete, terminating computation (`mpegRun`'s
  well-founded recursion does not reduce via plain kernel `whnf`/`decide`,
  the same known Lean 4 quirk documented in `Divergence.lean`'s and
  M-PEG-5's `Expand.lean`'s module docstrings — `simp` with the relevant
  equation lemmas drives the computation instead).
- **CE-002** (well-formedness ⇏ termination): `Divergence.lean`'s
  `selfCallDiverges` — a genuine proof, not a decide-based check (the
  claim itself is about non-termination, which no fuel bound could ever
  witness).
- **CE-003** (`MacroExpander` capture bug): NOT formalized in `MExp` at
  all — `MExp` is de Bruijn-indexed, so it has no bound-variable NAMES to
  shadow/capture in the first place; the bug is specific to the
  reference's NAME-based `substitute` (`MacroExpander.scala`), which this
  project's translation was deliberately designed to sidestep (see
  `MacroPeg/Syntax.lean`'s module docstring on `.lam`/capture). Documented
  here for the record, independently verified in Scala only
  (`scala/macro-peg-diff/`).

**Minimality, scoped honestly**: CE-002's minimality (no single rule can
exhibit this pattern) is a one-line code-inspection argument, not a
search — see `Divergence.lean`'s module docstring. CE-001's minimality (no
strictly smaller grammar, under the reference's own well-formedness rules,
shows strategy divergence) is NOT re-derived via an exhaustive
size-bounded search of a constructor whitelist in this round — that would
be a substantial, separate enumeration/search framework, and is left as
explicit future work rather than rushed. What IS established here is that
THIS witness genuinely exhibits the claimed divergence, machine-checked.
-/

namespace Shallot.MacroPeg

/-- **CE-001**: `S = F("a") !.; F(x) = "b";` (`F` never references its
parameter). Rule 0 is `S`, rule 1 is `F`. -/
def strategyDivergeGrammar : MGrammar :=
  { rules :=
      [ { arity := 0, body := .seq (.call 1 [.lit ['a']]) (.notP .any) }
      , { arity := 1, body := .lit ['b'] } ] }

/-- The input both reference-verified runs below share: `"ab"`. -/
def strategyDivergeInput : List Char := ['a', 'b']

/-- Under call-by-name, `F`'s actual parameter `"a"` is never forced (its
body `"b"` doesn't reference `x`), so `F("a")` matches literal `"b"`
against the CURRENT input `"ab"` — which fails (starts with `'a'`), and so
does the whole sequence. Reference-verified: `sbt console` on the
original surface grammar gives `Failure`. -/
theorem ce001_callByName :
    CmpOutcome.ofRun strategyDivergeGrammar .callByName 10
      (.call 0 []) strategyDivergeInput = .reject := by
  simp [CmpOutcome.ofRun, CmpOutcome.ofMOutcome, mpegRun,
    strategyDivergeGrammar, strategyDivergeInput, ruleAtM, MExp.subst, MExp.substArgs, argAt,
    stripPrefix?, beqChar]

/-- Under call-by-value-sequential, `F`'s actual parameter `"a"` is
evaluated FIRST against the original input (consuming it, leaving `"b"`),
and `F`'s body is then derived from that THREADED position — matching
literal `"b"` against `"b"` succeeds, consuming everything. Reference-
verified: `sbt console` gives `Success("")`. -/
theorem ce001_callByValueSeq :
    CmpOutcome.ofRun strategyDivergeGrammar .callByValueSeq 10
      (.call 0 []) strategyDivergeInput = .accept [] := by
  simp [CmpOutcome.ofRun, CmpOutcome.ofMOutcome, mpegRun, evalArgsSeq,
    strategyDivergeGrammar, strategyDivergeInput, ruleAtM, MExp.subst, MExp.substArgs, argAt,
    stripPrefix?, prefixBeforeSuffix, beqChar, lenChars]

/-- Under call-by-value-parallel, `F`'s actual parameter `"a"` is
evaluated against the ORIGINAL (un-threaded) input, and `F`'s body is
ALSO derived from that same original input — matching literal `"b"`
against `"ab"` fails, same as call-by-name. Reference-verified: `sbt
console` gives `Failure`. -/
theorem ce001_callByValuePar :
    CmpOutcome.ofRun strategyDivergeGrammar .callByValuePar 10
      (.call 0 []) strategyDivergeInput = .reject := by
  simp [CmpOutcome.ofRun, CmpOutcome.ofMOutcome, mpegRun, evalArgsPar,
    strategyDivergeGrammar, strategyDivergeInput, ruleAtM, MExp.subst, MExp.substArgs, argAt,
    stripPrefix?, prefixBeforeSuffix, beqChar, lenChars]

/-- **CE-001's headline**: the three strategies do not all agree — CBVSeq
diverges from CBN/CBVPar (which happen to coincide for this witness). -/
theorem ce001_strategies_disagree :
    CmpOutcome.ofRun strategyDivergeGrammar .callByValueSeq 10
        (.call 0 []) strategyDivergeInput ≠
      CmpOutcome.ofRun strategyDivergeGrammar .callByName 10
        (.call 0 []) strategyDivergeInput := by
  rw [ce001_callByValueSeq, ce001_callByName]
  decide

end Shallot.MacroPeg
