import Shallot.Peg.PalindromeEpsMiddle

/-!
# T7 evidence: ALL SIX priority orders of the peel-both-ends family fail

`Palindrome.lean`, `PalindromeEpsFirst.lean` and `PalindromeEpsMiddle.lean`
formalize three of the six possible orderings of the three ingredients
`aCase := "a" Pal "a"`, `bCase := "b" Pal "b"`, `epsCase := ε` inside
`Pal`'s `.alt` chain — one representative from each of the three
qualitatively distinct `ε`-placement classes (last / first / middle). The
other three orderings are exactly the `a ↔ b` swap of those three, and by
the grammar's total symmetry under swapping the characters `'a'` and
`'b'`, they fail for the mirror-image reason with the mirror-image
witness. This file completes the case analysis: EVERY one of the 6
possible single-nonterminal, peel-both-ends-with-these-three-ingredients
constructions is incomplete. This is a genuinely bounded but COMPLETE
result for this specific (small, natural) grammar family — not a proof of
`CFLSubsetPELConjecture` itself, but a full classification of the one
concrete family this project has explored by direct construction.

| order         | file                          | witness rejected  |
|---------------|-------------------------------|--------------------|
| a, b, ε       | `Palindrome.lean`              | `"aaaa"` (partial) |
| b, a, ε       | this file (`palBAEpsGrammar`)  | `"bbbb"` (partial) |
| ε, a, b       | `PalindromeEpsFirst.lean`      | every non-empty w  |
| ε, b, a       | this file (`palEpsBAGrammar`)  | every non-empty w  |
| a, ε, b       | `PalindromeEpsMiddle.lean`     | `"bb"` (b-case dead) |
| b, ε, a       | this file (`palBEpsAGrammar`)  | `"aa"` (a-case dead) |
-/

namespace Shallot

/-- `Pal ← "b" Pal "b" / "a" Pal "a" / ε` — the `a ↔ b` mirror of
`palBody`. -/
def palBAEpsBody : PExp :=
  .alt (.seq (.chr 'b') (.seq (.nt PalIdx) (.chr 'b')))
    (.alt (.seq (.chr 'a') (.seq (.nt PalIdx) (.chr 'a'))) .eps)

def palBAEpsGrammar : Grammar := { rules := [palBAEpsBody], start := PalIdx }

/-- Mirrors `palGrammar_aaaa_partial`: on `"bbbb"`, this grammar's
innermost recursive call closes off greedily on `ε` the same way
`palGrammar` does on `"aaaa"`, stranding the same way. -/
theorem palBAEps_bbbb_partial :
    ∃ t, pegRun palBAEpsGrammar 30 (.nt PalIdx) ['b', 'b', 'b', 'b']
      = some (.ok t ['b', 'b']) := by
  simp only [pegRun, palBAEpsGrammar, palBAEpsBody, ruleAt, PalIdx, beqChar]
  exact ⟨_, rfl⟩

theorem palBAEps_incomplete_on_bbbb :
    ¬ ∃ t, Derives palBAEpsGrammar (.nt PalIdx) ['b', 'b', 'b', 'b'] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨f, hf⟩ := pegRun_complete hderiv
  obtain ⟨t', hpartial⟩ := palBAEps_bbbb_partial
  have hf' := pegRun_mono_le (Nat.le_max_left f 30) hf
  have hpartial' := pegRun_mono_le (Nat.le_max_right f 30) hpartial
  rw [hf'] at hpartial'
  injection hpartial' with heq
  injection heq with _ hrest
  exact List.cons_ne_nil _ _ hrest.symm

/-- `Pal ← ε / "b" Pal "b" / "a" Pal "a"` — the `a ↔ b` mirror of
`palEpsFirstBody`. -/
def palEpsBABody : PExp :=
  .alt .eps
    (.alt (.seq (.chr 'b') (.seq (.nt PalIdx) (.chr 'b')))
      (.seq (.chr 'a') (.seq (.nt PalIdx) (.chr 'a'))))

def palEpsBAGrammar : Grammar := { rules := [palEpsBABody], start := PalIdx }

theorem palEpsBA_always_eps (w : List Char) :
    ∃ t, Derives palEpsBAGrammar (.nt PalIdx) w (.ok t w) :=
  ⟨_, .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _ (.eps w))⟩

theorem palEpsBA_rejects_nonempty {w : List Char} (hw : w ≠ []) :
    ¬ ∃ t, Derives palEpsBAGrammar (.nt PalIdx) w (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨t', hderiv'⟩ := palEpsBA_always_eps w
  have heq := derives_det hderiv hderiv'
  injection heq with _ hrest
  exact hw hrest.symm

/-- `Pal ← "b" Pal "b" / ε / "a" Pal "a"` — the `a ↔ b` mirror of
`palEpsMiddleBody`: now the `a-case` is the one made structurally
unreachable. -/
def palBEpsABody : PExp :=
  .alt (.seq (.chr 'b') (.seq (.nt PalIdx) (.chr 'b')))
    (.alt .eps (.seq (.chr 'a') (.seq (.nt PalIdx) (.chr 'a'))))

def palBEpsAGrammar : Grammar := { rules := [palBEpsABody], start := PalIdx }

theorem palBEpsA_bCase_fails_on_a {d : Char} (hd : d = 'a') (rest : List Char) :
    Derives palBEpsAGrammar (.seq (.chr 'b') (.seq (.nt PalIdx) (.chr 'b')))
      (d :: rest) .fail :=
  .seqFail₁ _ _ _ (.chrFail _ _ _ (by subst hd; decide))

theorem palBEpsA_eps_on_a {d : Char} (hd : d = 'a') (rest : List Char) :
    ∃ t, Derives palBEpsAGrammar (.nt PalIdx) (d :: rest) (.ok t (d :: rest)) :=
  ⟨_, .ntOk _ _ _ _ _ rfl
    (.altR _ _ _ _ _ (palBEpsA_bCase_fails_on_a hd rest) (.altL _ _ _ _ _ (.eps _)))⟩

/-- The mirror of `palEpsMiddle_rejects_bb`: `"aa"` is rejected here. -/
theorem palBEpsA_rejects_aa :
    ¬ ∃ t, Derives palBEpsAGrammar (.nt PalIdx) ['a', 'a'] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨t', hderiv'⟩ := palBEpsA_eps_on_a (rfl : 'a' = 'a') ['a']
  have heq := derives_det hderiv hderiv'
  injection heq with _ hrest
  exact List.cons_ne_nil _ _ hrest.symm

/-- **The headline, all six cases together**: every one of the 6
orderings of `{aCase, bCase, epsCase}` inside a single `.alt` chain fails
to recognize palindromes, each with an explicit rejected witness. This is
the complete case analysis for this one grammar family — the family is
exhaustively bad, not just the two representative instances tried first. -/
theorem all_six_peel_orders_incomplete :
    (¬ ∃ t, Derives palGrammar (.nt PalIdx) ['a','a','a','a'] (.ok t [])) ∧
    (¬ ∃ t, Derives palBAEpsGrammar (.nt PalIdx) ['b','b','b','b'] (.ok t [])) ∧
    (¬ ∃ t, Derives palEpsFirstGrammar (.nt PalIdx) ['a','a'] (.ok t [])) ∧
    (¬ ∃ t, Derives palEpsBAGrammar (.nt PalIdx) ['a','a'] (.ok t [])) ∧
    (¬ ∃ t, Derives palEpsMiddleGrammar (.nt PalIdx) ['b','b'] (.ok t [])) ∧
    (¬ ∃ t, Derives palBEpsAGrammar (.nt PalIdx) ['a','a'] (.ok t [])) :=
  ⟨palGrammar_incomplete_on_aaaa, palBAEps_incomplete_on_bbbb,
    palEpsFirst_rejects_nonempty (by simp), palEpsBA_rejects_nonempty (by simp),
    palEpsMiddle_rejects_bb, palBEpsA_rejects_aa⟩

end Shallot
