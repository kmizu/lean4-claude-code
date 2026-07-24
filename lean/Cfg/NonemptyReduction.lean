import Cfg.OpenProblems
import Shallot.Peg.GrammarExtend

/-!
# T7: routing around Ford's empty-string restriction on predicate elimination

`Shallot/Peg/GrammarExtend.lean` builds the machinery (`guardedGrammar`,
`guardedGrammar_iff`) for a new attack on `CFLSubsetPELConjecture`,
motivated by Ford's own POPL 2004 paper: Section 4.2 there proves that
any well-formed, predicate-and-repetition-carrying PEG grammar whose
language does NOT contain the empty string can be rewritten into an
equivalent predicate-free, repetition-free grammar (`PEG0`) — full PEG
and `PEG0` have EXACTLY the same expressive power once `ε` is excluded.
Symmetrically, a predicate-free grammar accepting `ε` must accept every
string (`ε ∈ L(G) ⟹ L(G) = Σ*`), which is precisely why the restriction
cannot simply be lifted.

`EvenPalindromes` (this project's leading candidate witness for
`¬CFLSubsetPELConjecture`) contains `ε`, so Ford's theorem doesn't apply
to it directly. This file proves the bridge: a plain PEG grammar for ANY
language `L` yields one for `L`'s non-empty restriction, essentially for
free (`isPEL_nonemptyRestriction_of_isPEL`). Combined (elsewhere) with Ford's
normal-form theorem — cited, not re-proved here, in the same spirit as
the classical non-context-freeness fact `cfl_proper_subset_mpel1` already
cites for aⁿbⁿcⁿ — and a genuine impossibility proof for `PEG0`
recognizing `EvenPalindromes \ {ε}`, this chains into:

```
  ¬IsPEL0 (EvenPalindromes \ {ε})        -- a PEG0-specific impossibility proof
  ⟹ ¬IsPEL (EvenPalindromes \ {ε})       -- via Ford's normal-form theorem (cited)
  ⟹ ¬IsPEL EvenPalindromes               -- via isPEL_nonempty_of_isPEL's contrapositive
  ⟹ ¬CFLSubsetPELConjecture              -- since EvenPalindromes is context-free
```

**Honest status**: only the LAST link (`isPEL_nonempty_of_isPEL`) is
proved in this file. The other links require either citing Ford's
normal-form theorem explicitly (not reproved here — a substantial
three-stage construction) or a genuine, still-open impossibility proof
for `PEG0`. This file does not itself resolve `CFLSubsetPELConjecture`.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp Grammar.SelfContained guardedGrammar
  guardedGrammar_iff guardedGrammar_selfContained)

/-- The non-empty restriction of a language: same membership, minus `ε`. -/
def NonemptyRestriction (L : Language) : Language := fun w => L w ∧ w ≠ []

/-- **The bridge lemma**: given ANY plain PEG grammar `g` for `L` (with
`g` self-contained and its start index in range — the natural
well-definedness conditions every concretely-built grammar in this
project already satisfies), `guardedGrammar g` is a plain PEG grammar for
`L`'s non-empty restriction. So if `L` is in `PEL`, so is its non-empty
restriction — witnessed constructively, not just asserted. -/
theorem isPEL_nonemptyRestriction_of_isPEL {L : Language} (g : Grammar)
    (hself : g.SelfContained) (hstart : g.start < g.rules.length)
    (hg : ∀ w, L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t [])) :
    IsPEL (NonemptyRestriction L) := by
  refine ⟨guardedGrammar g, fun w => ?_⟩
  rw [guardedGrammar_iff g hself hstart w]
  constructor
  · rintro ⟨hl, hne⟩
    obtain ⟨t, ht⟩ := (hg w).mp hl
    exact ⟨hne, t, ht⟩
  · rintro ⟨hne, t, ht⟩
    exact ⟨(hg w).mpr ⟨t, ht⟩, hne⟩

/-- Contrapositive form, the direction actually useful for attacking
`CFLSubsetPELConjecture`: if `L`'s non-empty restriction is NOT in `PEL`
(for every self-contained witness — see the module docstring for why
this scoping is honest and necessary), then `L` itself is not in `PEL`
either, for any self-contained grammar attempt. -/
theorem not_isPEL_of_not_isPEL_nonemptyRestriction {L : Language}
    (h : ¬ ∃ g : Grammar, g.SelfContained ∧ g.start < g.rules.length ∧
      ∀ w, NonemptyRestriction L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t [])) :
    ¬ ∃ g : Grammar, g.SelfContained ∧ g.start < g.rules.length ∧
      ∀ w, L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t []) := by
  rintro ⟨g, hself, hstart, hg⟩
  have hstart' : (guardedGrammar g).start < (guardedGrammar g).rules.length := by
    simp only [guardedGrammar, List.length_append, List.length_cons, List.length_nil]; omega
  refine h ⟨guardedGrammar g, guardedGrammar_selfContained g hself hstart, hstart', fun w => ?_⟩
  rw [guardedGrammar_iff g hself hstart w]
  constructor
  · rintro ⟨hl, hne⟩; obtain ⟨t, ht⟩ := (hg w).mp hl; exact ⟨hne, t, ht⟩
  · rintro ⟨hne, t, ht⟩; exact ⟨(hg w).mpr ⟨t, ht⟩, hne⟩

/-- `EvenPalindromes` genuinely contains the empty string — the fact that
makes Ford's normal-form theorem inapplicable to it directly, and hence
motivates routing through `NonemptyRestriction` in the first place. -/
theorem evenPalindromes_nil : EvenPalindromes [] := by
  unfold EvenPalindromes; decide

/-- **Specialized to the actual target**: if `EvenPalindromes` (minus its
one problematic empty-string member) is not in `PEL` — for any
self-contained grammar attempt — then `EvenPalindromes` itself is not in
`PEL` either, hence `¬CFLSubsetPELConjecture` (since `EvenPalindromes` is
context-free). This is the concrete instantiation of the chain in the
module docstring's last link; what remains is the (still open, see
`Shallot/Peg/MidpointObstruction.lean` for how far this project's methods
currently reach) impossibility proof for `NonemptyRestriction
EvenPalindromes` itself. -/
theorem not_isPEL_evenPalindromes_of_not_isPEL_nonempty
    (h : ¬ ∃ g : Grammar, g.SelfContained ∧ g.start < g.rules.length ∧
      ∀ w, NonemptyRestriction EvenPalindromes w ↔
        ∃ t, Derives g (.nt g.start) w (.ok t [])) :
    ¬ ∃ g : Grammar, g.SelfContained ∧ g.start < g.rules.length ∧
      ∀ w, EvenPalindromes w ↔ ∃ t, Derives g (.nt g.start) w (.ok t []) :=
  not_isPEL_of_not_isPEL_nonemptyRestriction h

end Shallot.Cfg
