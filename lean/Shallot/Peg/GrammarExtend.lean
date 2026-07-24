import Shallot.Peg.Semantics
import Shallot.Peg.Determinism
import Shallot.Peg.Examples

/-!
# T7: extending a grammar's rule list preserves its self-contained behavior

This file develops the machinery for a new attack on
`CFLSubsetPELConjecture`, following Ford's own POPL 2004 "Parsing
Expression Grammars: A Recognition-Based Syntactic Foundation": Section
4.2 there proves that any well-formed grammar whose language does NOT
include the empty string can be rewritten into an equivalent
predicate-free (and repetition-free) grammar — i.e. plain PEG with
lookahead/repetition and plain PEG WITHOUT them (`PEG0`) have EXACTLY the
same expressive power, once the empty string is excluded. Symmetrically,
Ford proves a predicate-free grammar accepting the empty string must
accept EVERY string (`ε ∈ L(G) ⟹ L(G) = Σ*`) — a striking, decisive fact
this project had not consulted the original paper for until now.

The strategy this enables: `EvenPalindromes` itself contains the empty
string, so Ford's normal-form theorem does not apply to it directly. But
`EvenPalindromes' := EvenPalindromes \ {ε}` does NOT contain the empty
string — so if `EvenPalindromes'` had a plain PEG grammar, Ford's theorem
would force it to have a PEG0 (predicate-free) grammar too. Combined with
a genuine impossibility proof for PEG0 (pursued separately), this could
resolve `CFLSubsetPELConjecture` for `EvenPalindromes` itself, via the
easy observation below (`guardedGrammar_iff`): a PEG grammar for
`EvenPalindromes` immediately yields one for `EvenPalindromes'` (guard
the start expression with a non-emptiness lookahead), so ruling out a
grammar for `EvenPalindromes'` rules one out for `EvenPalindromes` too.

**What this file proves, precisely**: given a grammar `g` all of whose
`.nt` references stay within its own rule list (`SelfContained` below —
a natural closure condition every concretely-constructed grammar in this
project already satisfies, since it is never assumed automatically by
the bare `Grammar` type), appending ONE new rule to `g.rules` and
pointing a fresh start expression at it (`guardedGrammar`) changes
NOTHING about how `g`'s original rules behave (`derives_append_preserved`
/ `derives_append_reflect`) — the new expression only ever gets to run
`g`'s original start expression, wrapped in a non-emptiness check
(`guardedGrammar_iff`).

**Honest scope note**: this file does NOT attempt to formalize Ford's
general predicate-elimination normal-form theorem itself (Sections
4.2.1–4.2.3 of the paper — a substantial three-stage construction). That
theorem is used, when needed, as an explicitly cited external fact, in
the same spirit as the classical non-context-freeness fact
`cfl_proper_subset_mpel1` already cites for aⁿbⁿcⁿ elsewhere in this
project — never smuggled in as an unproven `axiom`.
-/

namespace Shallot

/-- `e.NtBounded n` holds when every `.nt` reference inside `e` is a
valid index into a rule list of length `n` — i.e. `e` never reaches
"off the end" of such a list. -/
def PExp.NtBounded (n : Nat) : PExp → Prop
  | .eps => True
  | .any => True
  | .chr _ => True
  | .range _ _ => True
  | .lit _ => True
  | .nt i => i < n
  | .seq e1 e2 => e1.NtBounded n ∧ e2.NtBounded n
  | .alt e1 e2 => e1.NtBounded n ∧ e2.NtBounded n
  | .star e => e.NtBounded n
  | .notP e => e.NtBounded n

/-- A grammar is self-contained if every rule's `.nt` references stay
within the grammar's own rule list — the natural, if not automatically
enforced, well-definedness condition every concretely-built grammar in
this project satisfies (e.g. `palGrammar`, `midGrammar`, `abcGrammar`:
each rule only ever calls indices that exist in that same grammar). -/
def Grammar.SelfContained (g : Grammar) : Prop :=
  ∀ r ∈ g.rules, r.NtBounded g.rules.length

theorem ruleAt_append_left (l1 l2 : List PExp) (i : Nat) (h : i < l1.length) :
    ruleAt (l1 ++ l2) i = ruleAt l1 i := by
  induction l1 generalizing i with
  | nil => simp at h
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ i' => simp only [List.cons_append, ruleAt]; exact ih i' (by simp at h; omega)

theorem ruleAt_append_right (l1 : List PExp) (x : PExp) :
    ruleAt (l1 ++ [x]) l1.length = some x := by
  induction l1 with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, List.length_cons, ruleAt]; exact ih

theorem ruleAt_mem {l : List PExp} {i : Nat} {e : PExp} (h : ruleAt l i = some e) :
    e ∈ l := by
  induction l generalizing i with
  | nil => simp [ruleAt] at h
  | cons r rs ih =>
    cases i with
    | zero =>
        simp only [ruleAt] at h
        injection h with h; subst h
        exact List.mem_cons_self
    | succ i' => simp only [ruleAt] at h; exact List.mem_cons_of_mem r (ih h)

theorem ruleAt_lt_length {l : List PExp} {i : Nat} (h : i < l.length) :
    ∃ e, ruleAt l i = some e := by
  induction l generalizing i with
  | nil => simp at h
  | cons r rs ihl =>
    cases i with
    | zero => exact ⟨r, rfl⟩
    | succ i' =>
      simp only [List.length_cons] at h
      obtain ⟨e', he'⟩ := ihl (i := i') (by omega)
      exact ⟨e', he'⟩

/-- Appending rules to a grammar changes nothing about how any
`NtBounded`-within-range expression behaves — in particular, `g`'s own
rules (guarded by `SelfContained`) keep their exact original semantics.
The `start` field is irrelevant to `Derives` (it only ever consults
`rules`), so it is a free parameter here, chosen independently on each
side. -/
theorem derives_append_preserved {g : Grammar} (extra : List PExp) (s : Nat)
    {e : PExp} (he : e.NtBounded g.rules.length) (hself : g.SelfContained)
    {w : List Char} {o : Outcome} (h : Derives g e w o) :
    Derives { rules := g.rules ++ extra, start := s } e w o := by
  induction h with
  | eps input => exact .eps input
  | anyOk c rest => exact .anyOk c rest
  | anyFail => exact .anyFail
  | chrOk c d rest hcd => exact .chrOk c d rest hcd
  | chrFail c d rest hcd => exact .chrFail c d rest hcd
  | chrEmpty c => exact .chrEmpty c
  | rangeOk lo hi d rest hcond => exact .rangeOk lo hi d rest hcond
  | rangeFail lo hi d rest hcond => exact .rangeFail lo hi d rest hcond
  | rangeEmpty lo hi => exact .rangeEmpty lo hi
  | litOk s input rest hs => exact .litOk s input rest hs
  | litFail s input hs => exact .litFail s input hs
  | ntOk i e' input rest t hr hd ih =>
      have hi : i < g.rules.length := he
      have hr' : ruleAt (g.rules ++ extra) i = some e' := by
        rw [ruleAt_append_left g.rules extra i hi]; exact hr
      have he' : e'.NtBounded g.rules.length := hself e' (ruleAt_mem hr)
      exact .ntOk i e' input rest t hr' (ih he')
  | ntFail i e' input hr hd ih =>
      have hi : i < g.rules.length := he
      have hr' : ruleAt (g.rules ++ extra) i = some e' := by
        rw [ruleAt_append_left g.rules extra i hi]; exact hr
      have he' : e'.NtBounded g.rules.length := hself e' (ruleAt_mem hr)
      exact .ntFail i e' input hr' (ih he')
  | ntMissing i input hr =>
      exfalso
      have hi : i < g.rules.length := he
      obtain ⟨e', he'⟩ := ruleAt_lt_length hi
      rw [hr] at he'
      exact absurd he' (by simp)
  | seqOk e1 e2 input rest1 rest2 t1 t2 hd1 hd2 ih1 ih2 =>
      exact .seqOk e1 e2 input rest1 rest2 t1 t2 (ih1 he.1) (ih2 he.2)
  | seqFail₁ e1 e2 input hd1 ih1 => exact .seqFail₁ e1 e2 input (ih1 he.1)
  | seqFail₂ e1 e2 input rest1 t1 hd1 hd2 ih1 ih2 =>
      exact .seqFail₂ e1 e2 input rest1 t1 (ih1 he.1) (ih2 he.2)
  | altL e1 e2 input rest t hd ih => exact .altL e1 e2 input rest t (ih he.1)
  | altR e1 e2 input rest t hf hok ihf ihok =>
      exact .altR e1 e2 input rest t (ihf he.1) (ihok he.2)
  | altFail e1 e2 input hf1 hf2 ih1 ih2 =>
      exact .altFail e1 e2 input (ih1 he.1) (ih2 he.2)
  | starNil e input hf ih => exact .starNil e input (ih he)
  | starCons e input rest rest' t ts hd1 hd2 ih1 ih2 =>
      exact .starCons e input rest rest' t ts (ih1 he) (ih2 he)
  | notOk e input rest t hd ih => exact .notOk e input rest t (ih he)
  | notFail e input hf ih => exact .notFail e input (ih he)

/-- The converse of `derives_append_preserved`: since `e` never reaches
past `g.rules`, extra appended rules are simply never consulted, so a
derivation over the extended grammar reflects straight back down to one
over `g` alone. -/
theorem derives_append_reflect {g : Grammar} (extra : List PExp) (s : Nat)
    {e : PExp} (he : e.NtBounded g.rules.length) (hself : g.SelfContained)
    {w : List Char} {o : Outcome}
    (h : Derives { rules := g.rules ++ extra, start := s } e w o) :
    Derives g e w o := by
  induction h with
  | eps input => exact .eps input
  | anyOk c rest => exact .anyOk c rest
  | anyFail => exact .anyFail
  | chrOk c d rest hcd => exact .chrOk c d rest hcd
  | chrFail c d rest hcd => exact .chrFail c d rest hcd
  | chrEmpty c => exact .chrEmpty c
  | rangeOk lo hi d rest hcond => exact .rangeOk lo hi d rest hcond
  | rangeFail lo hi d rest hcond => exact .rangeFail lo hi d rest hcond
  | rangeEmpty lo hi => exact .rangeEmpty lo hi
  | litOk s input rest hs => exact .litOk s input rest hs
  | litFail s input hs => exact .litFail s input hs
  | ntOk i e' input rest t hr hd ih =>
      have hi : i < g.rules.length := he
      have hr' : ruleAt g.rules i = some e' := by
        rw [← ruleAt_append_left g.rules extra i hi]; exact hr
      have he' : e'.NtBounded g.rules.length := hself e' (ruleAt_mem hr')
      exact .ntOk i e' input rest t hr' (ih he')
  | ntFail i e' input hr hd ih =>
      have hi : i < g.rules.length := he
      have hr' : ruleAt g.rules i = some e' := by
        rw [← ruleAt_append_left g.rules extra i hi]; exact hr
      have he' : e'.NtBounded g.rules.length := hself e' (ruleAt_mem hr')
      exact .ntFail i e' input hr' (ih he')
  | ntMissing i input hr =>
      have hi : i < g.rules.length := he
      obtain ⟨e', he'⟩ := ruleAt_lt_length hi
      have hcontra : ruleAt (g.rules ++ extra) i = some e' := by
        rw [ruleAt_append_left g.rules extra i hi]; exact he'
      rw [hr] at hcontra
      exact absurd hcontra (by simp)
  | seqOk e1 e2 input rest1 rest2 t1 t2 hd1 hd2 ih1 ih2 =>
      exact .seqOk e1 e2 input rest1 rest2 t1 t2 (ih1 he.1) (ih2 he.2)
  | seqFail₁ e1 e2 input hd1 ih1 => exact .seqFail₁ e1 e2 input (ih1 he.1)
  | seqFail₂ e1 e2 input rest1 t1 hd1 hd2 ih1 ih2 =>
      exact .seqFail₂ e1 e2 input rest1 t1 (ih1 he.1) (ih2 he.2)
  | altL e1 e2 input rest t hd ih => exact .altL e1 e2 input rest t (ih he.1)
  | altR e1 e2 input rest t hf hok ihf ihok =>
      exact .altR e1 e2 input rest t (ihf he.1) (ihok he.2)
  | altFail e1 e2 input hf1 hf2 ih1 ih2 =>
      exact .altFail e1 e2 input (ih1 he.1) (ih2 he.2)
  | starNil e input hf ih => exact .starNil e input (ih he)
  | starCons e input rest rest' t ts hd1 hd2 ih1 ih2 =>
      exact .starCons e input rest rest' t ts (ih1 he) (ih2 he)
  | notOk e input rest t hd ih => exact .notOk e input rest t (ih he)
  | notFail e input hf ih => exact .notFail e input (ih he)

/-- `&any` (the and-predicate against "any single character") succeeds,
consuming nothing, exactly on non-empty input. -/
theorem andP_any_ok {g : Grammar} {c : Char} {rest : List Char} :
    Derives g (PExp.andP .any) (c :: rest) (.ok .notT (c :: rest)) :=
  .notFail _ _ (.notOk _ _ _ _ (.anyOk c rest))

theorem andP_any_fail {g : Grammar} : Derives g (PExp.andP .any) [] .fail :=
  .notOk _ _ _ _ (.notFail _ _ .anyFail)

/-- `&any (.nt start)` — check the input is non-empty (no consumption),
then hand off to the original start expression. -/
def guardedBody (start : Nat) : PExp := .seq (PExp.andP .any) (.nt start)

/-- `g` with one new rule appended: a fresh start expression that only
succeeds on non-empty input, and behaves exactly like `g`'s own start
expression otherwise. -/
def guardedGrammar (g : Grammar) : Grammar :=
  { rules := g.rules ++ [guardedBody g.start], start := g.rules.length }

/-- **The key reduction**: `guardedGrammar g` recognizes exactly the
non-empty strings `g` recognizes — nothing more, nothing less. This is
what lets a hypothetical PEG grammar for `EvenPalindromes` (which must
accept `ε`) be turned into one for `EvenPalindromes \ {ε}` (which must
not), the first step in routing around Ford's empty-string restriction
on predicate elimination. -/
theorem guardedGrammar_iff (g : Grammar) (hself : g.SelfContained)
    (hstart : g.start < g.rules.length) (w : List Char) :
    (∃ t, Derives (guardedGrammar g) (.nt (guardedGrammar g).start) w (.ok t [])) ↔
      (w ≠ [] ∧ ∃ t', Derives g (.nt g.start) w (.ok t' [])) := by
  constructor
  · rintro ⟨t, ht⟩
    cases ht with
    | ntOk _ _ _ _ _ hr hd =>
      have hre : ruleAt (guardedGrammar g).rules g.rules.length = some (guardedBody g.start) :=
        ruleAt_append_right g.rules (guardedBody g.start)
      simp only [guardedGrammar] at hr hre
      rw [hre] at hr
      injection hr with hr
      subst hr
      simp only [guardedBody] at hd
      obtain ⟨rest1, t1, t2, _, h1, h2⟩ := seq_inv hd
      cases w with
      | nil =>
        cases h1 with
        | notFail _ _ hfail =>
          cases hfail with
          | notOk _ _ _ _ hany => cases hany
      | cons c cs =>
        refine ⟨List.cons_ne_nil c cs, ?_⟩
        have heq : rest1 = c :: cs := by
          have hdd := derives_det h1 (andP_any_ok (g := guardedGrammar g) (c := c) (rest := cs))
          injection hdd with _ hrest
        subst heq
        have hnt : (PExp.nt g.start).NtBounded g.rules.length := hstart
        exact ⟨t2, derives_append_reflect [guardedBody g.start] g.rules.length hnt hself h2⟩
  · rintro ⟨hne, t', ht'⟩
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hnt : (PExp.nt g.start).NtBounded g.rules.length := hstart
    have ht'' := derives_append_preserved [guardedBody g.start] g.rules.length hnt hself ht'
    have hseq : Derives (guardedGrammar g) (guardedBody g.start) (c :: cs) (.ok _ []) :=
      .seqOk _ _ _ _ _ _ _ andP_any_ok ht''
    have hre : ruleAt (guardedGrammar g).rules g.rules.length = some (guardedBody g.start) :=
      ruleAt_append_right g.rules (guardedBody g.start)
    exact ⟨_, .ntOk _ _ _ _ _ hre hseq⟩

theorem PExp.NtBounded_mono {n m : Nat} (h : n ≤ m) {e : PExp} (he : e.NtBounded n) :
    e.NtBounded m := by
  induction e with
  | eps => trivial
  | any => trivial
  | chr _ => trivial
  | range _ _ => trivial
  | lit _ => trivial
  | nt i => simp only [PExp.NtBounded] at he ⊢; omega
  | seq e1 e2 ih1 ih2 => exact ⟨ih1 he.1, ih2 he.2⟩
  | alt e1 e2 ih1 ih2 => exact ⟨ih1 he.1, ih2 he.2⟩
  | star e ih => exact ih he
  | notP e ih => exact ih he

/-- `guardedGrammar g` is self-contained whenever `g` is — the one new
rule only ever calls `g.start`, which is within range by `hstart`, and
existing self-containment simply weakens along the longer rule list. -/
theorem guardedGrammar_selfContained (g : Grammar) (hself : g.SelfContained)
    (hstart : g.start < g.rules.length) : (guardedGrammar g).SelfContained := by
  intro r hr
  have hlen : (guardedGrammar g).rules.length = g.rules.length + 1 := by
    simp only [guardedGrammar, List.length_append, List.length_cons, List.length_nil]
  simp only [guardedGrammar] at hr
  rw [List.mem_append] at hr
  rcases hr with hr | hr
  · have hb := hself r hr
    rw [hlen]
    exact PExp.NtBounded_mono (by omega) hb
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [hlen]
    simp only [guardedBody, PExp.NtBounded]
    exact ⟨trivial, by omega⟩

end Shallot
