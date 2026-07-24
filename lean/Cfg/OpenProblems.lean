import Cfg.Properness

/-!
# T7: `CFL ⊆ PEL` (plain, macro-free PEG) — an open problem, documented not
solved

T3 (`Cfg/Properness.lean`) settles `CFL ⊊ MPEL^CBN_1` — the MACRO-extended
PEG class properly contains the context-free languages. This file is about
a DIFFERENT, older question that this project does **not** resolve: does
the PLAIN (macro-free) PEG class `PEL` also contain every CFL?

**What is actually settled here** (mechanized, below): `PEL ⊄ CFL` — the
aⁿbⁿcⁿ witness (`S_char`) is already sufficient, since `abcGrammar` is a
plain PEG grammar (no macro parameters at all) recognizing a language that
isn't context-free. This is the classical "PEG is not weaker than CFG"
half of the comparison, and it falls out of machinery already built for T3
almost for free.

**What remains open** (`CFLSubsetPELConjecture`, stated but never proved
or disproved): whether every context-free language is ALSO recognized by
some plain PEG. Ford's original POPL 2004 paper already conjectured PEG
might be strictly more expressive than CFG; Loff, Moreira and Reis
(DLT 2018 / JCSS) gave PEG's language class a complete characterization via
"scaffolding automata" but did not resolve this specific question, and (as
of this writing, no progress found post-2020) neither has anyone since. The
leading candidate witness is the language of even-length palindromes over
a 2-letter alphabet (`EvenPalindromes`, below) — trivially context-free,
conjectured to have no plain-PEG grammar — but no one has found a proof
technique that establishes the non-membership (pumping-lemma-style
arguments that work for CFL don't transparently carry over to PEG's
greedy, prioritized-choice semantics).

**Why T2's construction does not transfer to this question**: T2's CPS
embedding of a CFG into Macro PEG is essentially built on continuations —
`buildCallSeq` threads "what to try next if this succeeds" as an actual
argument passed to a parametrized rule call. A plain PEG rule has no
parameters at all, so it cannot receive a continuation this way; there is
no analogous mechanism to fall back on. This asymmetry (the macro layer's
extra expressiveness comes specifically from parametrized rules being able
to carry control-flow information as data) is itself worth noting as a
point of interest, not just a technical dead end.

Tackling `CFLSubsetPELConjecture` for real would need either a scaffolding-
automata-style pumping argument specific to PEG's semantics, or a genuinely
new technique — this file makes no attempt at either. Any future progress
should keep the "Conjecture" label (or a weaker "Bounded-survived: true up
to size N, exhaustively checked" label) until an actual proof exists —
never smuggled in as an unproven declaration or placeholder gap.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp abcGrammar S_char)

/-- `L` is recognized by some plain (macro-free) PEG grammar — Ford's class
`PEL`, using the same "and then end of input" convention as `IsCFL`. -/
def IsPEL (L : Language) : Prop :=
  ∃ (g : Grammar), ∀ w, L w ↔ ∃ t, Derives g (.nt g.start) w (.ok t [])

/-- The aⁿbⁿcⁿ witness is in `PEL` — `abcGrammar` is already a plain PEG
grammar (T1/T2's macro machinery is not needed at all here), so this falls
directly out of `S_char`. -/
theorem abc_isPEL : IsPEL abcLanguage := ⟨abcGrammar, fun w => (S_char w).symm⟩

/-- **Settled** (the "PEG is not weaker than CFG" half): `PEL ⊄ CFL`. Takes
the same non-context-freeness hypothesis for aⁿbⁿcⁿ as T3
(`cfl_proper_subset_mpel1`) — the classical pumping-lemma fact, supplied by
the caller rather than smuggled in. -/
theorem pel_not_subset_cfl (habc_not_cfl : ¬ IsCFL abcLanguage) :
    ¬ (∀ L : Language, IsPEL L → IsCFL L) :=
  fun h => habc_not_cfl (h abcLanguage abc_isPEL)

/-- **Open** (not proved or disproved by this project): does every
context-free language have a plain-PEG grammar? This is a bare `Prop`
definition, never a `theorem` — it pins down precisely what remains
unresolved without asserting an answer either way. -/
def CFLSubsetPELConjecture : Prop := ∀ L : Language, IsCFL L → IsPEL L

/-- The leading conjectured counterexample to `CFLSubsetPELConjecture`:
even-length palindromes over `{a, b}` — trivially context-free (a textbook
CFG: `S → aSa | bSb | ε`, not constructed here), conjectured to have no
plain-PEG grammar, with no known proof of that non-membership. Restricted
to `{a, b}` and even length to match the form the conjecture is usually
stated in; the general "any-alphabet, any-length" palindrome language is
an easy corollary of this restricted one being non-PEL (a plain-PEG
grammar for the general language would restrict to one for this one). -/
def EvenPalindromes : Language :=
  fun w => w.length % 2 = 0 ∧ w.all (fun c => c = 'a' ∨ c = 'b') ∧ w.reverse = w

end Shallot.Cfg
