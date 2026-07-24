import MacroPeg.Completeness

/-!
# CE-002: well-formedness ⇏ termination — `selfCallDiverges`

The reference `GrammarValidator.leadsToSelf` (`kmizu/macro_peg`,
`GrammarValidator.scala`/`Ast.scala`) detects left recursion only at the
FORMAL parameter level: its `Call`/`Identifier` cases check whether a name
equals the enclosing rule's own symbol, but a rule's own PARAMETER name
(e.g. `x` in `F(x) = x;`) is never traced back to whatever ACTUAL argument
expression was passed in at a call site. Consequently

```
S = F(S) !.;
F(x) = x;
```

passes `GrammarValidator.validate` (no left recursion is reported — `x`,
the identifier inside `F`'s body, is never `== S`), yet evaluating `S`
never terminates: under call-by-name, `F(S)`'s actual parameter `S` is
substituted UNEVALUATED for `x` in `F`'s body, so `F(S)`'s substituted
body is literally `S` again — `S → F(S) → S → F(S) → ⋯`, consuming zero
input at every step. This is the strongest evidence in the reference
implementation's counterexample set: it isn't a hypothetical edge case,
it's a grammar the shipped well-formedness checker itself accepts.

**Minimality**: one rule cannot exhibit this pattern at all. A single rule
`R(params) = body` calling itself directly is exactly what
`leadsToSelf`'s `Call(_, name, _) => if name == sym then true` clause
exists to catch (this is checked by direct inspection of the one-line
condition, not by brute-force search) — the loophole is specifically about
a call THROUGH an intermediate rule (`F` here) whose formal parameter gets
instantiated, at the call site, with a reference back to the ORIGINAL
rule. Two rules is therefore the minimum needed, and `S`/`F` above is
already minimal in that sense.

This file formalizes the grammar as `selfCallGrammar` (`Shallot.MacroPeg`'s
own `MExp`/`MGrammar`, not `kmizu/macro_peg`'s surface syntax) and proves
`selfCallDiverges`: no `MDerives` outcome exists for `.call 0 []` at any
input — a genuine non-termination fact, not merely "the interpreter runs
out of fuel at some bound." The proof works at the `mpegRun` (fuel-indexed
interpreter) level, where the loop is completely explicit and mechanical,
then transports the result to `MDerives` via `mpegRun_complete`'s
contrapositive (T3 from the base Macro PEG framework).
-/

namespace Shallot.MacroPeg

/-- `S = F(S) !.; F(x) = x;`, in this project's `MExp`/`MGrammar` — rule 0
is `S` (arity 0), rule 1 is `F` (arity 1). `S`'s body threads its own
0-arity self-reference as `F`'s actual parameter; `F`'s body is just
`.param 0` (the reference implementation's `F(x) = x`). -/
def selfCallGrammar : MGrammar :=
  { rules :=
      [ { arity := 0, body := .seq (.call 1 [.call 0 []]) (.notP .any) }
      , { arity := 1, body := .param 0 } ] }

/-- One full unwind of the loop consumes exactly 3 fuel units: `.call 0 []`
(rule lookup, `S`'s body) → `.seq`'s first branch, `.call 1 [.call 0 []]`
(rule lookup, substituting `.param 0 ↦ .call 0 []` into `F`'s body) →
back to `.call 0 []`, at 3 less fuel. Proved by strong induction on the
fuel bound, matching `A_char`/`B_char`'s `Nat.strongRecOn` style
(`Shallot/Peg/Examples.lean`) — the three base cases (fuel `0`, `1`, `2`)
each bottom out at the interpreter's own `fuel = 0 ↦ none` clause before a
full unwind completes; fuel `k + 3` unwinds exactly once and appeals to
the induction hypothesis at the strictly smaller `k`. -/
theorem selfCall_loop_none (input : List Char) :
    ∀ fuel, mpegRun selfCallGrammar .callByName fuel (.call 0 []) input = none := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    match fuel with
    | 0 => simp [mpegRun, selfCallGrammar, ruleAtM, MExp.subst, MExp.substArgs, argAt]
    | 1 => simp [mpegRun, selfCallGrammar, ruleAtM, MExp.subst, MExp.substArgs, argAt]
    | 2 => simp [mpegRun, selfCallGrammar, ruleAtM, MExp.subst, MExp.substArgs, argAt]
    | k + 3 =>
      show mpegRun selfCallGrammar .callByName (k + 3) (.call 0 []) input = none
      have hrec : mpegRun selfCallGrammar .callByName k (.call 0 []) input = none :=
        ih k (by omega)
      simp only [selfCallGrammar] at hrec ⊢
      simp [mpegRun, ruleAtM, MExp.subst, MExp.substArgs, argAt, hrec]

/-- **CE-002's headline**: no derivation of any outcome exists for `.call
0 []` (i.e. `S`) at any input — genuine non-termination, transported from
`selfCall_loop_none` via `mpegRun_complete`'s contrapositive (if some
`MDerives` outcome existed, some finite fuel bound would witness it). -/
theorem selfCallDiverges (input : List Char) :
    ¬ ∃ o, MDerives selfCallGrammar .callByName (.call 0 []) input o := by
  rintro ⟨o, hderiv⟩
  obtain ⟨f, hf⟩ := mpegRun_complete hderiv
  rw [selfCall_loop_none input f] at hf
  cases hf

end Shallot.MacroPeg
