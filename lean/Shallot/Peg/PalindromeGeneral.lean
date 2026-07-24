import Shallot.Peg.MidPointGeneral
import Shallot.Peg.Palindrome

/-!
# T7: `palGrammar`'s incompleteness, generalized over ANY 2-letter alphabet

`Palindrome.lean`'s `exists_palindrome_palGrammar_rejects` is a single
instance: the literal PEG transcription of `Pal → a Pal a | b Pal b | ε`
rejects `"aaaa"`. This file generalizes that ONE witness into a genuine
theorem, quantified over an arbitrary 2-letter alphabet `{c0, c1}`,
exactly mirroring `MidPointGeneral.lean`'s generalization of `midGrammar`:
for EVERY pair of distinct characters `c0 ≠ c1`, the direct transcription
`Pal ← c0 Pal c0 / c1 Pal c1 / ε` rejects `[c0, c0, c0, c0]` (four
repeats of `c0`) — a genuine (even-length) palindrome, matching exactly
`"aaaa"`'s failure for `(c0, c1) = ('a', 'b')`.

The trace (verified by direct computation before formalizing, same
discipline as every prior counterexample in this project):

```
Pal([])           = ε,        rest = []            (both peel alts fail: empty input)
Pal([c0])         = ε,        rest = [c0]           (both peel alts fail: no room for trail)
Pal([c0,c0])      = peel c0,  rest = []              (uses Pal([c0])'s ε-result as the middle)
Pal([c0,c0,c0])   = ε,        rest = [c0,c0,c0]      (peel alt fails: Pal([c0,c0]) leaves no room for trail)
Pal([c0,c0,c0,c0]) = peel c0, rest = [c0,c0]         (uses Pal([c0,c0,c0])'s ε-result as the middle)
```

The mechanism is exactly `palGrammar_incomplete_on_aaaa`'s — the
innermost recursive call at odd residual length commits to `ε` (no other
alternative can succeed on it), and that commitment then propagates
outward, stranding two characters at the end — but proved here without
ever inspecting what `c0`/`c1` actually are, only that they differ.
-/

namespace Shallot

/-- `Pal ← c0 Pal c0 / c1 Pal c1 / ε`, generalizing `palBody` over an
arbitrary 2-letter alphabet `{c0, c1}`. -/
def genPalBody (c0 c1 : Char) : PExp :=
  .alt (.seq (.chr c0) (.seq (.nt PalIdx) (.chr c0)))
    (.alt (.seq (.chr c1) (.seq (.nt PalIdx) (.chr c1))) .eps)

def genPalGrammar (c0 c1 : Char) : Grammar := { rules := [genPalBody c0 c1], start := PalIdx }

/-- `Pal` on the empty input succeeds via `ε` (both peel alternatives
need `≥ 1` character). -/
theorem genPal_empty (c0 c1 : Char) :
    Derives (genPalGrammar c0 c1) (.nt PalIdx) [] (.ok (.nodeNT PalIdx (.choiceR (.choiceR (.leaf [])))) []) :=
  .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
    (.seqFail₁ _ _ _ (.chrEmpty _))
    (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrEmpty _)) (.eps [])))

/-- `Pal` on a single `c0` succeeds via `ε`, leaving `[c0]` unconsumed:
the first alternative needs a trailing `c0` after the (empty, via
`genPal_empty`) inner `Pal` call, but there's nothing left to match it
against; the second alternative's leading character doesn't match. -/
theorem genPal_c0_singleton {c0 c1 : Char} (hne : c0 ≠ c1) :
    ∃ t, Derives (genPalGrammar c0 c1) (.nt PalIdx) [c0] (.ok t [c0]) := by
  have hc1c0 : beqChar c1 c0 = false := beqChar_ne (Ne.symm hne)
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  refine ⟨_, .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
    (.seqFail₂ _ _ _ _ _ (.chrOk _ _ _ hc0c0)
      (.seqFail₂ _ _ _ _ _ (genPal_empty c0 c1) (.chrEmpty _)))
    (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrFail _ _ _ hc1c0)) (.eps _)))⟩

/-- `Pal` on `[c0, c0]` succeeds via the FIRST alternative, fully
consuming both characters: the leading `c0` is consumed, the inner `Pal`
call on the leftover `[c0]` succeeds via `ε` (`genPal_c0_singleton`,
consuming nothing, leaving `[c0]`), and that leftover `c0` matches the
required trailing `c0`. -/
theorem genPal_c0c0 {c0 c1 : Char} (hne : c0 ≠ c1) :
    ∃ t, Derives (genPalGrammar c0 c1) (.nt PalIdx) [c0, c0] (.ok t []) := by
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  obtain ⟨t0, ht0⟩ := genPal_c0_singleton hne
  exact ⟨_, .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _
    (.seqOk _ _ _ _ _ _ _ (.chrOk _ _ _ hc0c0)
      (.seqOk _ _ _ _ _ _ _ ht0 (.chrOk _ _ _ hc0c0))))⟩

/-- `Pal` on `[c0, c0, c0]` succeeds via `ε`, leaving all three
characters unconsumed: the first alternative's inner `Pal` call on
`[c0, c0]` succeeds FULLY (via `genPal_c0c0`, leaving `[]`), so the
required trailing `c0` has nothing left to match — the first alternative
fails; the second alternative's leading character doesn't match. -/
theorem genPal_c0c0c0 {c0 c1 : Char} (hne : c0 ≠ c1) :
    ∃ t, Derives (genPalGrammar c0 c1) (.nt PalIdx) [c0, c0, c0] (.ok t [c0, c0, c0]) := by
  have hc1c0 : beqChar c1 c0 = false := beqChar_ne (Ne.symm hne)
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  obtain ⟨t0, ht0⟩ := genPal_c0c0 hne
  refine ⟨_, .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
    (.seqFail₂ _ _ _ _ _ (.chrOk _ _ _ hc0c0) (.seqFail₂ _ _ _ _ _ ht0 (.chrEmpty _)))
    (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrFail _ _ _ hc1c0)) (.eps _)))⟩

/-- `Pal` on `[c0, c0, c0, c0]` succeeds via the FIRST alternative, but
only PARTIALLY: the leading `c0` is consumed, the inner `Pal` call on the
leftover `[c0,c0,c0]` succeeds via `ε` (`genPal_c0c0c0`, consuming
nothing, leaving all three `c0`s), and the FIRST of those leftover `c0`s
matches the required trailing `c0` — leaving the other two unconsumed. -/
theorem genPal_c0c0c0c0_partial {c0 c1 : Char} (hne : c0 ≠ c1) :
    ∃ t, Derives (genPalGrammar c0 c1) (.nt PalIdx) [c0, c0, c0, c0] (.ok t [c0, c0]) := by
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  obtain ⟨t0, ht0⟩ := genPal_c0c0c0 hne
  exact ⟨_, .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _
    (.seqOk _ _ _ _ _ _ _ (.chrOk _ _ _ hc0c0)
      (.seqOk _ _ _ _ _ _ _ ht0 (.chrOk _ _ _ hc0c0))))⟩

/-- **The headline, generalized over any 2-letter alphabet**: for ANY two
distinct characters `c0 ≠ c1`, the direct PEG transcription of `Pal → c0
Pal c0 | c1 Pal c1 | ε` rejects `[c0, c0, c0, c0]` — a genuine
palindrome — outright, generalizing `palGrammar_incomplete_on_aaaa`'s
`"aaaa"` for `(c0, c1) = ('a', 'b')` to EVERY possible alphabet at once.
Proved by determinism: `genPal_c0c0c0c0_partial` fixes what `Pal` ACTUALLY
does on this input (partial match, leaving `[c0, c0]`), which is
incompatible with any hypothetical full match (leaving `[]`). -/
theorem genPal_rejects_c0c0c0c0 {c0 c1 : Char} (hne : c0 ≠ c1) :
    ¬ ∃ t, Derives (genPalGrammar c0 c1) (.nt PalIdx) [c0, c0, c0, c0] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨t', hderiv'⟩ := genPal_c0c0c0c0_partial hne
  have heq := derives_det hderiv hderiv'
  injection heq with _ hrest
  exact List.cons_ne_nil _ _ hrest.symm

end Shallot
