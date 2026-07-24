import Shallot.Peg.MidPoint
import Shallot.Peg.Examples

/-!
# T7: a general theorem — PEG cannot locate the midpoint, for ANY alphabet

`MidPoint.lean` exhibits ONE witness (`"bab"`) showing the direct PEG
transcription of `S → a S a | b S a | a` rejects a string whose only
requirement (middle character `= 'a'`) is context-free and imposes no
end-matching constraint at all. This file GENERALIZES that single
instance into a genuine theorem, quantified over an arbitrary 2-letter
alphabet: for ANY two distinct characters `c0 ≠ c1`, the analogous
grammar `S ← c0 S c0 / c1 S c0 / c0` rejects `[c1, c0, c1]` — the same
failure, for every possible choice of alphabet, not just `{'a','b'}`.

**Why this is the right level of generality for "PEG cannot find the
midpoint" as a theorem**: the underlying mechanism is `derives_det` —
`S`'s behavior on a given residual suffix is a function of that suffix
ALONE, with no way to know how many characters have already been
consumed (equivalently, no way to know "distance from the START of the
input", as opposed to "distance from the END", which the suffix's own
length DOES encode — exactly what `Helper`/`IAmPowerTwoLength` in
`PowerTwoHelper.lean` exploits). Concretely: the innermost recursive
call, on the shortest residual suffix where recursion becomes
structurally impossible, is FORCED to fall back to the fixed base case —
a decision made without any knowledge of whether this is the
"linguistically correct" stopping depth for the particular original
input. Since this argument never inspects the SPECIFIC identity of
`'a'`/`'b'`, only that they are distinct, it holds for every alphabet — a
genuine universally-quantified theorem, not a family of isolated
instances.

**Scope, stated honestly**: this rules out the "peel-recurse-with-fixed-
base" construction family for ANY choice of characters — it does NOT
prove `¬CFLSubsetPELConjecture` in general, since it says nothing about
constructions using absolute end-distance tricks (Theorem 8's escape
hatch) or any other approach not of this shape.
-/

namespace Shallot

/-- `S ← c0 S c0 / c1 S c0 / c0`, generalizing `midBody` over an arbitrary
2-letter alphabet `{c0, c1}`. -/
def genMidBody (c0 c1 : Char) : PExp :=
  .alt (.seq (.chr c0) (.seq (.nt MidIdx) (.chr c0)))
    (.alt (.seq (.chr c1) (.seq (.nt MidIdx) (.chr c0)))
      (.chr c0))

def genMidGrammar (c0 c1 : Char) : Grammar := { rules := [genMidBody c0 c1], start := MidIdx }

theorem beqChar_refl (c : Char) : beqChar c c = true := by simp [beqChar]

theorem beqChar_ne {c d : Char} (h : c ≠ d) : beqChar c d = false := by
  rcases hb : beqChar c d with _ | _
  · rfl
  · exact absurd (beqChar_eq hb) h

/-- `MidIdx` fails outright on the empty input: both recursive
alternatives need `≥ 1` character for their leading `.chr`, and the base
case does too. -/
theorem genMid_fails_empty (c0 c1 : Char) :
    Derives (genMidGrammar c0 c1) (.nt MidIdx) [] .fail :=
  .ntFail _ _ _ rfl (.altFail _ _ _
    (.seqFail₁ _ _ _ (.chrEmpty _))
    (.altFail _ _ _ (.seqFail₁ _ _ _ (.chrEmpty _)) (.chrEmpty _)))

/-- `MidIdx` on `[c1]` fails outright: the first alternative needs a
leading `c0` (absent, since the head is `c1 ≠ c0`); the second consumes
the leading `c1` but then requires `MidIdx` to succeed on `[]` (it can't,
`genMid_fails_empty`); the base case needs a leading `c0` too. -/
theorem genMid_fails_c1 {c0 c1 : Char} (hne : c0 ≠ c1) :
    Derives (genMidGrammar c0 c1) (.nt MidIdx) [c1] .fail := by
  have hc0c1 : beqChar c0 c1 = false := beqChar_ne hne
  have hc1c1 : beqChar c1 c1 = true := beqChar_refl c1
  exact .ntFail _ _ _ rfl (.altFail _ _ _
    (.seqFail₁ _ _ _ (.chrFail _ _ _ hc0c1))
    (.altFail _ _ _
      (.seqFail₂ _ _ _ _ _ (.chrOk _ _ _ hc1c1)
        (.seqFail₁ _ _ _ (genMid_fails_empty c0 c1)))
      (.chrFail _ _ _ hc0c1)))

/-- `MidIdx` on `[c0, c1]`: the first alternative's inner recursive call
(`MidIdx` on `[c1]`) fails (`genMid_fails_c1`), so the whole first
alternative fails; the second alternative's leading character doesn't
match (head is `c0`, not `c1`); only the BASE CASE fires, consuming just
the leading `c0` and leaving `[c1]` unconsumed. -/
theorem genMid_c0c1_base {c0 c1 : Char} (hne : c0 ≠ c1) :
    ∃ t, Derives (genMidGrammar c0 c1) (.nt MidIdx) [c0, c1] (.ok t [c1]) := by
  have hc0c1 : beqChar c0 c1 = false := beqChar_ne hne
  have hc1c0 : beqChar c1 c0 = false := beqChar_ne (Ne.symm hne)
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  refine ⟨_, .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
    (.seqFail₂ _ _ _ _ _ (.chrOk _ _ _ hc0c0) (.seqFail₁ _ _ _ (genMid_fails_c1 hne)))
    (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrFail _ _ _ hc1c0)) (.chrOk _ _ _ hc0c0)))⟩

/-- `MidIdx` on `[c1, c0, c1]` fails outright: the first alternative needs
a leading `c0` (head is `c1`); the second consumes the leading `c1`, then
`MidIdx` on `[c0, c1]` succeeds via the base case leaving `[c1]`
(`genMid_c0c1_base`), but the required trailing `c0` doesn't match the
leftover `c1`; the base case itself needs a leading `c0`. -/
theorem genMid_fails_c1c0c1 {c0 c1 : Char} (hne : c0 ≠ c1) :
    Derives (genMidGrammar c0 c1) (.nt MidIdx) [c1, c0, c1] .fail := by
  have hc0c1 : beqChar c0 c1 = false := beqChar_ne hne
  have hc1c0 : beqChar c1 c0 = false := beqChar_ne (Ne.symm hne)
  have hc1c1 : beqChar c1 c1 = true := beqChar_refl c1
  obtain ⟨t0, ht0⟩ := genMid_c0c1_base hne
  exact .ntFail _ _ _ rfl (.altFail _ _ _
    (.seqFail₁ _ _ _ (.chrFail _ _ _ hc0c1))
    (.altFail _ _ _
      (.seqFail₂ _ _ _ _ _ (.chrOk _ _ _ hc1c1)
        (.seqFail₂ _ _ _ _ _ ht0 (.chrFail _ _ _ hc0c1)))
      (.chrFail _ _ _ hc0c1)))

/-- **The headline, generalized over any 2-letter alphabet**: for ANY two
distinct characters `c0 ≠ c1`, the direct PEG transcription of `S → c0 S
c0 | c1 S c0 | c0` rejects `[c1, c0, c1]` outright — the same failure
`midGrammar_rejects_bab` exhibits for `(c0, c1) = ('a', 'b')`, now proved
for EVERY possible alphabet at once. The middle character `c0` is
genuinely present, and the two `c1` end characters genuinely match each
other — this grammar just cannot locate the midpoint to stop the
recursion there. -/
theorem genMid_rejects_c1c0c1 {c0 c1 : Char} (hne : c0 ≠ c1) :
    ¬ ∃ t, Derives (genMidGrammar c0 c1) (.nt MidIdx) [c1, c0, c1] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  have := derives_det hderiv (genMid_fails_c1c0c1 hne)
  exact Outcome.noConfusion this

end Shallot
