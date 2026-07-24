import Shallot.Peg.Soundness
import Shallot.Peg.Completeness
import Shallot.Peg.Determinism
import Shallot.Peg.Examples

/-!
# T7 evidence: the textbook palindrome CFG, read as a plain PEG, is unsound-free
but INCOMPLETE

`CFLSubsetPELConjecture` (`Cfg/OpenProblems.lean`) asks whether every context-free
language has a plain-PEG grammar. The natural first attempt for even-length
palindromes over `{a, b}` is to transcribe the textbook CFG

```
Pal → a Pal a | b Pal b | ε
```

literally into PEG surface syntax (`Pal ← "a" Pal "a" / "b" Pal "b" / ε`) and hope
Ford's prioritized-choice semantics just happen to agree with the CFG's
(unambiguous, for this grammar) derivation. They do NOT, in general — this file
formalizes why, machine-checked, as a genuine data point toward the open
conjecture (not a resolution of it).

**What actually happens, mechanically** (confirmed first by direct computation
outside Lean, then reproduced here): PEG's `/` commits to whichever alternative
succeeds LOCALLY first, with no way to retroactively ask an already-successful
sub-derivation to consume less so an OUTER pending match can complete. For a run
of identical characters, the innermost recursive call greedily closes itself off
as its own self-contained `"a" Pal "a"` (or `"b" Pal "b"`) match, which can strand
the characters an OUTER pending match still needs. The concrete witness: `"aaaa"`
is a genuine (even-length) palindrome, but `palGrammar` — this exact literal
transcription — provably does not derive a full match for it.

Exhaustive computation (Python, outside this Lean development, not itself a
proof) found this pattern is remarkably ONE-SIDED: checking all strings over
`{a, b}` up to length 20, this grammar never accepts a NON-palindrome (zero false
positives found), only rejects some genuine ones (many false negatives, `"aaaa"`
being the shortest). That asymmetry is suggestive — it hints this specific
construction style might be *sound* in general (a real theorem, not attempted
here) even though it is provably not *complete* (which IS proven below) — but
soundness alone does not decide `CFLSubsetPELConjecture`; a complete PEG grammar
for palindromes, via any construction, is what the conjecture actually needs.
-/

namespace Shallot

/-- Rule index for `Pal` — the only nonterminal in this grammar. -/
def PalIdx : Nat := 0

/-- `Pal ← "a" Pal "a" / "b" Pal "b" / ε`, the literal PEG transcription of the
textbook palindrome CFG. -/
def palBody : PExp :=
  .alt (.seq (.chr 'a') (.seq (.nt PalIdx) (.chr 'a')))
    (.alt (.seq (.chr 'b') (.seq (.nt PalIdx) (.chr 'b'))) .eps)

def palGrammar : Grammar := { rules := [palBody], start := PalIdx }

/-- The obvious notion of a `List Char` being a palindrome. -/
def IsListPalindrome (w : List Char) : Prop := w.reverse = w

/-- The witness: `"aaaa"` is a genuine palindrome. -/
theorem aaaa_isPalindrome : IsListPalindrome ['a', 'a', 'a', 'a'] := rfl

/-- What the fuel-indexed interpreter actually computes for `Pal` on `"aaaa"`,
at a fuel bound generous enough to terminate: a PARTIAL match consuming only
the first two characters (`"aa"`), leaving `"aa"` unconsumed. This is the
"innermost recursive call greedily closes itself off" behavior described in
the module docstring, computed here exactly as `mpegRun`/`pegRun`-style
functions were elsewhere in this project — via `simp` unfolding the fuel-
indexed interpreter's equation lemmas, since `pegRun`'s well-founded recursion
does not reduce under plain kernel `rfl`/`decide` (the same known quirk
documented in `MacroPeg/Divergence.lean`). -/
theorem palGrammar_aaaa_partial :
    ∃ t, pegRun palGrammar 30 (.nt PalIdx) ['a', 'a', 'a', 'a']
      = some (.ok t ['a', 'a']) := by
  simp only [pegRun, palGrammar, palBody, ruleAt, PalIdx, beqChar]
  exact ⟨_, rfl⟩

/-- **The headline**: `palGrammar` — the literal PEG transcription of the
textbook palindrome CFG — does NOT derive a full match for `"aaaa"`, even
though `"aaaa"` genuinely is a palindrome. Proved from the computed partial
match above, via `pegRun_complete`'s contrapositive: if a full match existed,
`pegRun` would eventually report it (`pegRun_complete`), and since `pegRun` is
a deterministic function whose already-reached answers are stable under more
fuel (`pegRun_mono_le`), it would have to agree with the partial-match answer
already computed at a smaller fuel bound — but `.ok t []` (full match) and
`.ok t' ['a','a']` (partial match) are different outcomes (different `rest`),
a contradiction. -/
theorem palGrammar_incomplete_on_aaaa :
    ¬ ∃ t, Derives palGrammar (.nt PalIdx) ['a', 'a', 'a', 'a'] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨f, hf⟩ := pegRun_complete hderiv
  obtain ⟨t', hpartial⟩ := palGrammar_aaaa_partial
  have hf' := pegRun_mono_le (Nat.le_max_left f 30) hf
  have hpartial' := pegRun_mono_le (Nat.le_max_right f 30) hpartial
  rw [hf'] at hpartial'
  injection hpartial' with heq
  injection heq with _ hrest
  exact List.cons_ne_nil _ _ hrest.symm

/-- **T7's evidence, stated cleanly**: there exists a palindrome that a plain
PEG grammar — namely the literal transcription of the textbook CFG — fails to
recognize. This does NOT prove `¬CFLSubsetPELConjecture` (a cleverer grammar,
not of this literal-transcription shape, might still work — the conjecture
remains genuinely open, see `Cfg/OpenProblems.lean`), but it does rule out the
single most natural proof-by-construction attempt, machine-checked rather than
merely asserted. -/
theorem exists_palindrome_palGrammar_rejects :
    ∃ w, IsListPalindrome w ∧ ¬ ∃ t, Derives palGrammar (.nt PalIdx) w (.ok t []) :=
  ⟨['a', 'a', 'a', 'a'], aaaa_isPalindrome, palGrammar_incomplete_on_aaaa⟩

/-! ## The complementary result: `palGrammar` is SOUND (even though incomplete)

`exists_palindrome_palGrammar_rejects` shows this construction is not a
solution to `CFLSubsetPELConjecture`. It is natural to ask whether it is at
least a *safe* approximation — never wrongly accepting a non-palindrome. The
exhaustive computation described in the module docstring found zero false
positives up to length 20; this section proves that is not a coincidence of
small inputs, but holds for every input, by induction on `w.length`. -/

/-- Wrapping a palindrome with the same character on both ends is still a
palindrome — the one-line algebraic fact the induction below rests on. -/
theorem wrap_isListPalindrome {c : Char} {p : List Char} (hp : IsListPalindrome p) :
    IsListPalindrome (c :: p ++ [c]) := by
  simp only [IsListPalindrome, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, IsListPalindrome] at hp ⊢
  simp [hp]

/-- **Soundness**: whatever `palGrammar` matches is always ITSELF a
palindrome — proved by strong induction on the input length, unfolding one
layer of the grammar (`ntOk` then the `.alt`/`.alt`/`.eps` structure of
`palBody`, using `seq_inv`'s flat-existential inversion for each `.seq`,
matching this project's established style for avoiding `cases`-name-
clobbering in deeply nested derivations — see the memory note on this from
earlier PEG-example proofs) per branch, then applying the induction
hypothesis to the strictly shorter recursive `.nt PalIdx` sub-derivation. -/
theorem palGrammar_sound : ∀ (len : Nat) (w : List Char), w.length = len →
    ∀ (rest : List Char) (t : PTree), Derives palGrammar (.nt PalIdx) w (.ok t rest) →
    ∃ p, w = p ++ rest ∧ IsListPalindrome p := by
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
    intro w hlen rest t hderiv
    cases hderiv with
    | ntOk _ _ _ _ _ hr hd =>
        simp only [palGrammar, ruleAt, PalIdx] at hr
        injection hr with hr
        subst hr
        simp only [palBody] at hd
        cases hd with
        | altL _ _ _ _ _ hA =>
            obtain ⟨restA1, t1, t2, _, h1, h2⟩ := seq_inv hA
            cases h1 with
            | chrOk _ d _ hbeq =>
                have hdEq : d = 'a' := (beqChar_eq hbeq).symm
                subst hdEq
                obtain ⟨restA2, t3, t4, _, h3, h4⟩ := seq_inv h2
                cases h4 with
                | chrOk _ d' _ hbeq' =>
                    have hdEq' : d' = 'a' := (beqChar_eq hbeq').symm
                    subst hdEq'
                    have hlt : restA1.length < len := by
                      have : ('a' :: restA1).length = len := hlen
                      simp only [List.length_cons] at this; omega
                    obtain ⟨p, hpeq, hppal⟩ := ih restA1.length hlt restA1 rfl ('a' :: rest) t3 h3
                    refine ⟨'a' :: p ++ ['a'], ?_, wrap_isListPalindrome hppal⟩
                    show 'a' :: restA1 = 'a' :: p ++ ['a'] ++ rest
                    rw [hpeq]
                    simp
        | altR _ _ _ _ _ _ hNotA =>
            cases hNotA with
            | altL _ _ _ _ _ hB =>
                obtain ⟨restB1, t1, t2, _, h1, h2⟩ := seq_inv hB
                cases h1 with
                | chrOk _ d _ hbeq =>
                    have hdEq : d = 'b' := (beqChar_eq hbeq).symm
                    subst hdEq
                    obtain ⟨restB2, t3, t4, _, h3, h4⟩ := seq_inv h2
                    cases h4 with
                    | chrOk _ d' _ hbeq' =>
                        have hdEq' : d' = 'b' := (beqChar_eq hbeq').symm
                        subst hdEq'
                        have hlt : restB1.length < len := by
                          have : ('b' :: restB1).length = len := hlen
                          simp only [List.length_cons] at this; omega
                        obtain ⟨p, hpeq, hppal⟩ := ih restB1.length hlt restB1 rfl ('b' :: rest) t3 h3
                        refine ⟨'b' :: p ++ ['b'], ?_, wrap_isListPalindrome hppal⟩
                        show 'b' :: restB1 = 'b' :: p ++ ['b'] ++ rest
                        rw [hpeq]
                        simp
            | altR _ _ _ _ _ _ hEps =>
                cases hEps with
                | eps _ => exact ⟨[], rfl, rfl⟩

/-- Soundness, stated directly at the "whole input matched" case that
actually matters for recognizing a language (`rest = []`): `palGrammar`
never accepts a non-palindrome. Combined with `exists_palindrome_
palGrammar_rejects`, this pins down EXACTLY what this natural construction
achieves: `{w | Derives palGrammar (.nt PalIdx) w (.ok _ [])} ⊊
IsListPalindrome` (a proper subset — sound, but strictly incomplete). -/
theorem palGrammar_accepts_only_palindromes {w : List Char} {t : PTree}
    (h : Derives palGrammar (.nt PalIdx) w (.ok t [])) : IsListPalindrome w := by
  obtain ⟨p, hpeq, hppal⟩ := palGrammar_sound w.length w rfl [] t h
  rw [List.append_nil] at hpeq
  rwa [hpeq]

end Shallot
