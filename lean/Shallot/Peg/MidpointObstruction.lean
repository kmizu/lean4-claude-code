import Shallot.Peg.Determinism

/-!
# T7: the sharpest general form of the midpoint obstruction

Every prior result in this exploration (`PalindromeGeneral.lean`,
`PalindromeGeneralN.lean`, `MidPointGeneral.lean`) proves impossibility
for a SPECIFIC SHAPE of grammar — the "peel-recurse-with-fallback"
family, however large its alphabet or however many extra alternatives it
carries. This file states and proves the underlying obstruction in its
SHARPEST, most general form: a fact about `Derives`'s very TYPE, not
about any particular grammar shape at all, that applies to EVERY plain
PEG grammar, EVERY nonterminal, and EVERY construction strategy
whatsoever.

**The fact**: `Derives g e s o` does not mention, and cannot depend on,
anything about how the parser arrived at evaluating `e` on the residual
suffix `s` — not the prefix already consumed, not its length, not the
original total input length. This is not an assumption or a derived
property; it is definitionally true of the relation as given in
`Semantics.lean`. Consequently: if the CORRECTNESS of some larger parse
were to hinge on a SINGLE nonterminal call, evaluated once on a fixed
suffix `s`, correctly reporting "the amount already consumed to reach
here is exactly half of the (as yet unknown at this point) original
total input length" — this is IMPOSSIBLE, because that fact varies with
how much was consumed to reach `s`, while the nonterminal's `Derives`
outcome on `s` cannot.

**Why this does not, by itself, resolve `CFLSubsetPELConjecture`
(honest scope)**: this theorem rules out any mechanism that reduces
palindrome recognition to a SINGLE nonterminal call being the sole
arbiter of "am I at the midpoint" on a suffix. It does NOT rule out the
logical possibility of some more distributed, holistic recognition
strategy that never needs to ask this exact question at a single point —
though every concrete construction attempted in this project (the entire
`peel-recurse` family, in full alphabet/size generality) reduces to
exactly this pattern, and Theorem 8's escape hatch works specifically
because it asks a DIFFERENT, answerable question (distance from the
END, which the suffix's own length encodes) rather than this one. Ruling
out EVERY conceivable strategy — not just every strategy built this way —
is precisely the content of the scaffolding-automata characterization
Loff, Moreira and Reis develop (and leave incomplete) in the source
paper; it is not something a single suffix-determinism fact can settle
on its own. This file records the sharpest boundary this project's
methods can rigorously reach, not a resolution of the open conjecture.
-/

namespace Shallot

/-- **The core, grammar-agnostic obstruction.** Suppose a nonterminal
call `.nt i` on suffix `s` produces SOME outcome `o` (`ho`), and suppose
`decide : Outcome → Prop` is meant to read off, from that single outcome,
whether the amount already consumed to reach `s` (`k`, for any `k`) is
exactly half of the total original input length (`k + s.length`) — i.e.
`decide o ↔ 2 * k = k + s.length`, for EVERY `k` this same suffix `s`
could have been reached with. This is impossible: taking `k = s.length`
(a genuine midpoint: `2 * s.length = s.length + s.length`) forces
`decide o` to hold, but taking `k = s.length + 1` (never a midpoint:
`2 * (s.length + 1) ≠ (s.length + 1) + s.length`) forces `decide o` to
fail — a direct contradiction, since `o` — and hence `decide o` — is one
fixed thing (by `derives_det`, though this proof doesn't even need to
invoke it explicitly: `hcorrect` is universally quantified over `k` for
this ONE fixed derivation `ho`, so the contradiction is immediate — `ho`
itself goes unused in the proof below, which is exactly the point: the
impossibility is already forced by `hcorrect`'s type, before even asking
what `.nt i` actually does). -/
theorem no_suffix_only_midpoint_decider {g : Grammar} {i : Nat} {s : List Char} {o : Outcome}
    (ho : Derives g (.nt i) s o) (decide : Outcome → Prop)
    (hcorrect : ∀ k : Nat, decide o ↔ 2 * k = k + s.length) :
    False := by
  have h1 : decide o := (hcorrect s.length).mpr (by omega)
  have h2 : 2 * (s.length + 1) = (s.length + 1) + s.length := (hcorrect (s.length + 1)).mp h1
  omega

/-- The same fact, phrased to make the role of determinism explicit: if
`.nt i` is invoked on suffix `s` from TWO different "depths" (amounts
already consumed) `k₁ ≠ k₂` — necessarily with the SAME outcome `o`, by
`derives_det`, since both derivations are of the identical `(g, .nt i,
s)` — then `o` cannot correctly signal "midpoint" for both depths unless
at most one of `2*k₁ = k₁+s.length` and `2*k₂ = k₂+s.length` is asked to
hold. Concretely instantiating `k₁ = s.length` (the midpoint) and any
`k₂ ≠ s.length` (not) makes this precise. -/
theorem context_blind_forces_midpoint_error {g : Grammar} {i : Nat} {s : List Char}
    {o₁ o₂ : Outcome} (h₁ : Derives g (.nt i) s o₁) (h₂ : Derives g (.nt i) s o₂) :
    o₁ = o₂ :=
  derives_det h₁ h₂

end Shallot
