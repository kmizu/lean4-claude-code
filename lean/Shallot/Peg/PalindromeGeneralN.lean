import Shallot.Peg.PalindromeGeneral

/-!
# T7: `palGrammar`'s incompleteness, generalized over an ALPHABET OF ANY SIZE

`PalindromeGeneral.lean` generalizes `palGrammar_incomplete_on_aaaa` over
an arbitrary 2-letter alphabet. This file pushes the generalization
further, along a different axis: the ALPHABET SIZE. For `Pal ← c0 Pal c0
/ c1 Pal c1 / c2 Pal c2 / ... / cₘ Pal cₘ / ε` — an ARBITRARY number `m`
of "peel" alternatives, over an ARBITRARY alphabet, as long as all the
peel characters are distinct from the target character `c0` — the
grammar still rejects `[c0, c0, c0, c0]`. Verified computationally first
(same discipline as every counterexample in this project) across
alphabets of size 2, 3, and 5: the result is IDENTICAL regardless of how
many extra alternatives are present, because on an all-`c0` input, every
alternative whose leading character isn't `c0` fails immediately and
contributes nothing — the mechanism is entirely about the `c0`
alternative and the `ε` fallback; extra alternatives are simply inert.

The key extra lemma this requires beyond `PalindromeGeneral.lean`:
whatever the LIST of other (non-`c0`) peel alternatives looks like — one
character, five characters, any finite list, as long as none of them
equals `c0` — trying them all against an input starting with `c0` fails
every one of them in turn and falls through to `ε`, consuming nothing.
This holds independent of the grammar `g` (no recursive `.nt` call is
ever reached, since every leading-character check fails outright), which
is what makes the generalization to an unbounded list of alternatives
tractable: extending the list costs nothing to the proof once this
"all extra alternatives are inert on a c0-headed input" fact is
established once, by induction on the list.
-/

namespace Shallot

/-- One "peel" alternative for character `c`: `c Pal c`. -/
def peelAlt (c : Char) : PExp := .seq (.chr c) (.seq (.nt PalIdx) (.chr c))

/-- A chain of peel alternatives over `cs`, falling back to `ε` once the
list is exhausted: `c₁ Pal c₁ / c₂ Pal c₂ / ... / ε`. -/
def peelChain : List Char → PExp
  | [] => .eps
  | c :: rest => .alt (peelAlt c) (peelChain rest)

/-- `Pal ← c0 Pal c0 / (peelChain cs)` — an arbitrary number of extra peel
alternatives (for the characters in `cs`) appended after the distinguished
`c0` alternative, falling back to `ε`. -/
def genPalGrammarN (c0 : Char) (cs : List Char) : Grammar :=
  { rules := [.alt (peelAlt c0) (peelChain cs)], start := PalIdx }

/-- **Key lemma**: on ANY input headed by `c0`, a chain of peel
alternatives for characters ALL DIFFERENT from `c0` fails every single
one of them (each leading-character check fails outright, without ever
reaching the recursive `.nt` call) and falls through to `ε`, consuming
nothing. Holds for ANY grammar `g` (irrelevant here, since no `.nt` call
is ever evaluated) and ANY such list `cs`, by induction on `cs`. -/
theorem peelChain_eps_on_c0 (c0 : Char) : ∀ (cs : List Char), (∀ c ∈ cs, c ≠ c0) →
    ∀ (g : Grammar) (rest : List Char),
      ∃ t, Derives g (peelChain cs) (c0 :: rest) (.ok t (c0 :: rest)) := by
  intro cs
  induction cs with
  | nil => intro _ g rest; exact ⟨_, .eps _⟩
  | cons c cs' ih =>
    intro hall g rest
    have hcne : c ≠ c0 := hall c List.mem_cons_self
    have hcc0 : beqChar c c0 = false := beqChar_ne hcne
    obtain ⟨t, ht⟩ := ih (fun c' hc' => hall c' (List.mem_cons_of_mem c hc')) g rest
    exact ⟨_, .altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrFail _ _ _ hcc0)) ht⟩

/-- `peelChain cs` on the EMPTY input, for ANY `cs`: every peel
alternative's leading `.chr` fails on empty input (`chrEmpty`), so the
chain falls through to `ε`. No distinctness hypothesis needed. -/
theorem peelChain_eps_on_empty : ∀ (cs : List Char) (g : Grammar),
    ∃ t, Derives g (peelChain cs) [] (.ok t []) := by
  intro cs
  induction cs with
  | nil => intro g; exact ⟨_, .eps _⟩
  | cons c cs' ih =>
    intro g
    obtain ⟨t, ht⟩ := ih g
    exact ⟨_, .altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrEmpty _)) ht⟩

theorem genPalN_empty (c0 : Char) (cs : List Char) :
    ∃ t, Derives (genPalGrammarN c0 cs) (.nt PalIdx) [] (.ok t []) := by
  obtain ⟨t, ht⟩ := peelChain_eps_on_empty cs (genPalGrammarN c0 cs)
  exact ⟨_, .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrEmpty _)) ht)⟩

theorem genPalN_singleton {c0 : Char} {cs : List Char} (hall : ∀ c ∈ cs, c ≠ c0) :
    ∃ t, Derives (genPalGrammarN c0 cs) (.nt PalIdx) [c0] (.ok t [c0]) := by
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  obtain ⟨te, hte⟩ := genPalN_empty c0 cs
  obtain ⟨tc, htc⟩ := peelChain_eps_on_c0 c0 cs hall (genPalGrammarN c0 cs) []
  exact ⟨_, .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
    (.seqFail₂ _ _ _ _ _ (.chrOk _ _ _ hc0c0)
      (.seqFail₂ _ _ _ _ _ hte (.chrEmpty _)))
    htc)⟩

theorem genPalN_c0c0 {c0 : Char} {cs : List Char} (hall : ∀ c ∈ cs, c ≠ c0) :
    ∃ t, Derives (genPalGrammarN c0 cs) (.nt PalIdx) [c0, c0] (.ok t []) := by
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  obtain ⟨t0, ht0⟩ := genPalN_singleton hall
  exact ⟨_, .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _
    (.seqOk _ _ _ _ _ _ _ (.chrOk _ _ _ hc0c0)
      (.seqOk _ _ _ _ _ _ _ ht0 (.chrOk _ _ _ hc0c0))))⟩

theorem genPalN_c0c0c0 {c0 : Char} {cs : List Char} (hall : ∀ c ∈ cs, c ≠ c0) :
    ∃ t, Derives (genPalGrammarN c0 cs) (.nt PalIdx) [c0, c0, c0] (.ok t [c0, c0, c0]) := by
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  obtain ⟨t0, ht0⟩ := genPalN_c0c0 hall
  obtain ⟨tc, htc⟩ := peelChain_eps_on_c0 c0 cs hall (genPalGrammarN c0 cs) [c0, c0]
  exact ⟨_, .ntOk _ _ _ _ _ rfl (.altR _ _ _ _ _
    (.seqFail₂ _ _ _ _ _ (.chrOk _ _ _ hc0c0) (.seqFail₂ _ _ _ _ _ ht0 (.chrEmpty _)))
    htc)⟩

theorem genPalN_c0c0c0c0_partial {c0 : Char} {cs : List Char} (hall : ∀ c ∈ cs, c ≠ c0) :
    ∃ t, Derives (genPalGrammarN c0 cs) (.nt PalIdx) [c0, c0, c0, c0] (.ok t [c0, c0]) := by
  have hc0c0 : beqChar c0 c0 = true := beqChar_refl c0
  obtain ⟨t0, ht0⟩ := genPalN_c0c0c0 hall
  exact ⟨_, .ntOk _ _ _ _ _ rfl (.altL _ _ _ _ _
    (.seqOk _ _ _ _ _ _ _ (.chrOk _ _ _ hc0c0)
      (.seqOk _ _ _ _ _ _ _ ht0 (.chrOk _ _ _ hc0c0))))⟩

/-- **The headline, generalized over BOTH the alphabet identity AND its
size**: for ANY character `c0`, and ANY (finite, arbitrary-length) list
`cs` of characters all distinct from `c0`, the grammar `Pal ← c0 Pal c0 /
(peel alternatives for cs) / ε` — with as many extra "distractor"
alternatives as one likes — rejects `[c0, c0, c0, c0]`. The alphabet size
is completely irrelevant to the failure: extra alternatives for
characters other than `c0` are simply never reached on an all-`c0`
input, so they change nothing about the mechanism `palGrammar` (the
`cs = ['b']` case) already exhibits. -/
theorem genPalN_rejects_c0c0c0c0 {c0 : Char} {cs : List Char} (hall : ∀ c ∈ cs, c ≠ c0) :
    ¬ ∃ t, Derives (genPalGrammarN c0 cs) (.nt PalIdx) [c0, c0, c0, c0] (.ok t []) := by
  rintro ⟨t, hderiv⟩
  obtain ⟨t', hderiv'⟩ := genPalN_c0c0c0c0_partial hall
  have heq := derives_det hderiv hderiv'
  injection heq with _ hrest
  exact List.cons_ne_nil _ _ hrest.symm

end Shallot
