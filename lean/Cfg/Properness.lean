import Cfg.Cps
import MacroPeg.PegEmbed
import MacroPeg.Determinism
import Shallot.Peg.Examples

/-!
# T3: `CFL ⊊ MPEL^CBN_1` — Macro PEG (order ≤ 1) properly contains the
context-free languages

Combines T1 (`MacroPeg/PegEmbed.lean`, plain PEG embeds into arity-0 Macro
PEG) + T2 (`Cfg/Cps.lean`, GNF CFG embeds into arity-1 Macro PEG) + the
aⁿbⁿcⁿ witness (`Shallot/Peg/Examples.lean`'s `S_char`, a non-context-free
language a plain PEG recognizes):

- **Subset direction** (`gnf_cfl_subset_mpel1`): every GNF-representable CFG
  embeds into MPEL1. Honest scope, stated up front rather than glossed over:
  the textbook "every CFL ⊆ MPEL1" needs classical CFG→GNF normalization
  (eliminating ε/unit/left-recursive productions), which is cited but not
  formalized here (see `Cfg/Syntax.lean`'s module docstring) — this
  theorem's hypothesis is `isGnfB cg = true`, not "for an arbitrary CFG".
- **Properness witness** (`abc_isMPEL1` + `cfl_proper_subset_mpel1`): the
  aⁿbⁿcⁿ language is in MPEL1 (via T1, embedding `abcGrammar`) but NOT a CFL
  (the pumping-lemma fact, taken as an explicit hypothesis rather than an
  unproven declaration or placeholder gap — matching this project's policy:
  the caller must supply the classical non-context-freeness proof).

**Not proved here**: `CFL ⊆ PEL` (plain, macro-free PEG) is a genuinely open
problem (the palindrome conjecture) — T2's CPS construction is essentially
tied to the macro layer's continuation-passing power (an ordinary PEG rule
cannot receive "what to do next" as an argument), so it does not transfer to
that question. See `docs/roadmap.md`/`docs/theorems.md` (T7) for the
open-problem writeup.
-/

namespace Shallot.Cfg

open Shallot.MacroPeg (MExp MTree MGrammar MRule MDerives MOutcome Strategy
  embedExp embedTree embedOutcome embedOutcome_ok_inv pegToMacroPeg
  peg_embed_complete peg_embed_sound mderives_det)
open Shallot (PExp PTree Outcome Derives abcGrammar Sidx S_char)

/-- An order-≤1 (first-order) Macro PEG grammar: every rule has arity at
most 1 — the fragment both T1 (arity 0, plain PEG embedding) and T2 (arity
1, CFG embedding) actually land in. -/
def order1 (mg : MGrammar) : Prop := ∀ r ∈ mg.rules, r.arity ≤ 1

/-- `L` is recognized by some order-≤1 Macro PEG grammar under
call-by-name: `L ∈ MPEL^CBN_1`. -/
def IsMPEL1 (L : Language) : Prop :=
  ∃ (mg : MGrammar) (e : MExp), order1 mg ∧
    ∀ w, L w ↔ ∃ t, MDerives mg .callByName e w (.ok t [])

/-! ## `.notP .any` as an "end of input" check — used by T2's headline to
pin the continuation's leftover position to `[]`. -/

theorem notAny_success (g : CFGrammar) :
    MDerives (cfgToMacroPeg g) .callByName (.notP .any) [] (.ok .notT []) :=
  MDerives.notFail .any [] MDerives.anyFail

theorem notAny_not_fail (g : CFGrammar) :
    ¬ MDerives (cfgToMacroPeg g) .callByName (.notP .any) [] .fail := by
  intro hf
  exact MOutcome.noConfusion (mderives_det hf (notAny_success g))

theorem notAny_total (g : CFGrammar) : ∀ pos : List Char, Total g (.notP .any) pos
  | [] => Or.inr ⟨.notT, [], notAny_success g⟩
  | c :: cs => Or.inl (MDerives.notOk .any (c :: cs) cs (.leaf [c]) (MDerives.anyOk c cs))

/-- Any success of `.notP .any` forces its own input to be `[]` (the ONLY
way `.any` can fail) and leaves the position unchanged. -/
theorem notAny_ok_inv {g : CFGrammar} {pos : List Char} {t : MTree} {rest : List Char}
    (h : MDerives (cfgToMacroPeg g) .callByName (.notP .any) pos (.ok t rest)) :
    t = .notT ∧ rest = pos ∧ pos = [] := by
  cases h with
  | notFail _ _ hAnyFail =>
      cases hAnyFail with
      | anyFail => exact ⟨rfl, rfl, rfl⟩

/-- T2's headline, packaged at the language level: a GNF CFG's language
embeds into MPEL1 — witnessed by `cfgToMacroPeg cg` (all rules arity 1)
run against the continuation `.notP .any` ("and then end of input"). -/
theorem gnf_cfl_subset_mpel1 {cg : CFGrammar} (hgnf : isGnfB cg = true) :
    IsMPEL1 cg.language := by
  refine ⟨cfgToMacroPeg cg, cfgStartExpr cg, ?_, ?_⟩
  · intro r hr
    simp only [cfgToMacroPeg, List.mem_map] at hr
    obtain ⟨alts, _, hreq⟩ := hr
    rw [← hreq]; simp
  · intro w
    simp only [cfgStartExpr]
    constructor
    · intro hgen
      have hcomplete := cfg_cps_complete hgnf hgen (.notP .any) [] w.length
        (by simp) (fun pos _ => notAny_total cg pos) (notAny_not_fail cg)
      obtain ⟨t, rest, hderiv⟩ := hcomplete
      rw [List.append_nil] at hderiv
      obtain ⟨w', mid', hsplit, hgen', tk, hktk⟩ := cfg_cps_sound hgnf hderiv
      obtain ⟨_, hresteq, hmideq⟩ := notAny_ok_inv hktk
      rw [hmideq] at hresteq
      rw [hresteq] at hderiv
      exact ⟨t, hderiv⟩
    · rintro ⟨t, hderiv⟩
      obtain ⟨w', mid', hsplit, hgen', tk, hktk⟩ := cfg_cps_sound hgnf hderiv
      obtain ⟨_, _, hmideq⟩ := notAny_ok_inv hktk
      rw [hmideq, List.append_nil] at hsplit
      rwa [hsplit]

/-! ## The aⁿbⁿcⁿ witness: in MPEL1 (via T1) but not context-free. -/

/-- The aⁿbⁿcⁿ language — `S_char`'s witness, T3's example of a member of
`MPEL1 \ CFL`. -/
def abcLanguage : Language :=
  fun w => ∃ n, 1 ≤ n ∧ w = List.replicate n 'a' ++ List.replicate n 'b' ++ List.replicate n 'c'

/-- The aⁿbⁿcⁿ language is in MPEL1 — embed `abcGrammar` via T1 (arity-0
rules) and transport `S_char`'s exact characterization through
`peg_embed_complete`/`peg_embed_sound`. -/
theorem abc_isMPEL1 : IsMPEL1 abcLanguage := by
  refine ⟨pegToMacroPeg abcGrammar, .call Sidx [], ?_, ?_⟩
  · intro r hr
    simp only [pegToMacroPeg, List.mem_map] at hr
    obtain ⟨e, _, hreq⟩ := hr
    rw [← hreq]; simp
  · intro w
    constructor
    · intro hw
      obtain ⟨t, hderiv⟩ := S_char w |>.mpr hw
      exact ⟨embedTree t, peg_embed_complete hderiv⟩
    · rintro ⟨t', hderiv⟩
      obtain ⟨o', hoeq, hde⟩ := peg_embed_sound hderiv (.nt Sidx) rfl
      obtain ⟨t'', ht''eq, _⟩ := embedOutcome_ok_inv hoeq.symm
      subst ht''eq
      exact (S_char w).mp ⟨t'', hde⟩

/-- T3's headline: `MPEL^CBN_1` properly contains `CFL`. The non-CFL fact
for aⁿbⁿcⁿ is an explicit hypothesis (the classical pumping-lemma argument,
cited not re-derived — matching this project's discipline of never
smuggling in an unproven declaration or placeholder gap: the caller
supplies it). -/
theorem cfl_proper_subset_mpel1
    (habc_not_cfl : ¬ IsCFL abcLanguage) :
    (∀ cg : CFGrammar, isGnfB cg = true → IsMPEL1 cg.language) ∧
      (∃ L, IsMPEL1 L ∧ ¬ IsCFL L) :=
  ⟨fun _ hgnf => gnf_cfl_subset_mpel1 hgnf, abcLanguage, abc_isMPEL1, habc_not_cfl⟩

end Shallot.Cfg
