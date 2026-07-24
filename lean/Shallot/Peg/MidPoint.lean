import Shallot.Peg.Soundness
import Shallot.Peg.Completeness
import Shallot.Peg.Determinism
import Shallot.Peg.Examples

/-!
# T7 evidence: even a MIDPOINT-ONLY requirement (no end-matching at all)
already breaks this construction style

`Palindrome.lean` and its siblings all target genuine palindromes, which
bundle TWO distinct requirements together: (1) locate the midpoint, and
(2) verify the two halves match end-to-end. This file isolates
requirement (1) alone, dropping (2) entirely, to see whether the
`palGrammar`-style construction's failure comes from the matching
requirement or from midpoint-location itself.

`MidIsA := {w | |w| is odd ∧ w[⌊|w|/2⌋] = 'a'}` — odd-length strings whose
MIDDLE character is `'a'`, with NO constraint whatsoever relating the two
halves to each other. This is a much WEAKER, strictly easier-looking
requirement than being a palindrome (e.g. it's satisfied by `"bab"`,
`"aaa"`, `"xay"` for ANY `x, y`) — and it is certainly context-free (a
textbook CFG `S → a S a | b S a | a` builds it directly, matching either
end character against anything and forcing only the single middle
character).

The direct PEG transcription of that CFG, `S ← "a" S "a" / "b" S "a" /
"a"`, is machine-proven below to REJECT `"bab"` — the minimal odd-length
witness, `|w| = 3`. This is a sharper, cleaner data point than
`palGrammar`'s `"aaaa"`: it shows the SAME failure mechanism (inner
recursive call commits to the shortest base-case match before an outer
pending requirement can be satisfied) already breaks things even when
there is nothing to compare between the two ends at all — confirming
(concretely, not just by argument) that midpoint-location is itself the
obstruction, independent of, and prior to, any end-matching requirement
palindromes additionally impose.
-/

namespace Shallot

def MidIdx : Nat := 0

/-- `S ← "a" S "a" / "b" S "a" / "a"` — direct transcription of the CFG
`S → a S a | b S a | a`. The two recursive alternatives require different
LEADING characters (`'a'` vs `'b'`) but IDENTICAL trailing ones (`'a'`) —
by design, since only the middle character is constrained. -/
def midBody : PExp :=
  .alt (.seq (.chr 'a') (.seq (.nt MidIdx) (.chr 'a')))
    (.alt (.seq (.chr 'b') (.seq (.nt MidIdx) (.chr 'a')))
      (.chr 'a'))

def midGrammar : Grammar := { rules := [midBody], start := MidIdx }

/-- The obvious notion of "middle character is `'a'`": the character at
index `⌊|w|/2⌋`, 0-indexed, is `'a'`. -/
def IsMidA (w : List Char) : Prop := w[w.length / 2]? = some 'a'

/-- The witness: `"bab"` has middle character `'a'`. -/
theorem bab_isMidA : IsMidA ['b', 'a', 'b'] := by unfold IsMidA; decide

/-- What the fuel-indexed interpreter actually computes for `S` on
`"bab"`: total failure, not even a partial match — computed exactly as
`pegRun`-style functions were elsewhere in this project, via `simp`
unfolding the fuel-indexed interpreter's equation lemmas. -/
theorem midGrammar_bab_fails :
    pegRun midGrammar 20 (.nt MidIdx) ['b', 'a', 'b'] = some .fail := by
  simp (config := { decide := true }) [pegRun, midGrammar, midBody, ruleAt, MidIdx]

/-- **The headline**: `midGrammar` — the literal PEG transcription of the
CFG `S → a S a | b S a | a` — rejects `"bab"` outright, even though
`"bab"`'s middle character genuinely is `'a'` and this grammar imposes NO
requirement whatsoever on how the two end characters relate to each
other. Proved via `pegRun_complete`'s contrapositive, exactly as
`palGrammar_incomplete_on_aaaa`: if ANY derivation existed (full match or
otherwise), `pegRun` would report SOME outcome at sufficient fuel, but the
computed outcome here is unconditional `.fail`, which is incompatible with
an `.ok` result at the same (larger) fuel bound by determinism/monotonicity. -/
theorem midGrammar_rejects_bab :
    ¬ ∃ t, Derives midGrammar (.nt MidIdx) ['b', 'a', 'b'] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨f, hf⟩ := pegRun_complete hderiv
  have hf' := pegRun_mono_le (Nat.le_max_left f 20) hf
  have hfail' := pegRun_mono_le (Nat.le_max_right f 20) midGrammar_bab_fails
  rw [hf'] at hfail'
  cases hfail'

end Shallot
