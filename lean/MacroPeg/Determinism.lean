import MacroPeg.Semantics

/-!
# T2 — determinism of the macro-PEG derivation relation (call-by-name + call-by-value-par)

`MDerives g s e x o₁ → MDerives g s e x o₂ → o₁ = o₂`. Since `MOutcome.ok`
carries the parse tree, this gives parse-tree uniqueness for free.

## Why a combined recursor

`MDerives` is now `mutual` with `DerivesArgsPar` (see `MacroPeg/Semantics.lean`),
so `induction h₁ generalizing o₂` is rejected ("the induction tactic does not
support ... mutually inductive"). The fix is the explicit combined recursor
`MDerives.rec` with a real second motive — exactly the template in
`MacroPeg/Props.lean`, but here `motive_2` must be non-trivial: determinism of
`.call` under `.callByValuePar` needs determinism of `DerivesArgsPar` itself,
which can only be proved AS PART of the same mutual induction.

`motive_2` is a CONJUNCTION carrying the two facts about a successful
`DerivesArgsPar g s input args vals` derivation that the `.callByValuePar`
`.call` cases consume:

1. **value-list uniqueness** — two derivations for the same `g s input args`
   force the same `vals` (needed to line up `callParOk` vs `callParOk`, where
   the body is derived from `MExp.subst vals r.body`);
2. **every element succeeds** — for every `a ∈ args`, every outcome of `a` on
   `input` is `.ok` (needed to refute `callParOk`/`callParFail` against a
   `callParArgFail` that claims some argument failed).

Both are provable in the mutual `cons` case using the motive_1 IH of the head
sub-derivation (determinism of `a`) and the motive_2 IH of the tail. The
symmetric refutation (`callParArgFail` as the FIRST derivation, against a
`callParOk` whose `hargs'` has no IH) instead uses the standalone
`derivesArgsPar_mem_ok` below together with `callParArgFail`'s own motive_1 IH.

## Proof style for the shared cases

The strategy-independent constructors (`eps`/`any*`/`chr*`/`range*`/`lit*`/
`seq*`/`alt*`/`star*`/`not*`/`dbg`/`paramFail`/`callMissing`/`callArity`) are a
rule-for-rule transcription of `Shallot.derives_det`. Rule-lookup clashes die on
`ruleAtM g.rules i` (`rw [hr] at hr'; injection hr'`), arity clashes on
`r.arity = args.length` vs `≠` (`absurd`), cross-strategy clashes on the
`hs`/`hs'` `Strategy` equalities (`absurd (hs.symm.trans hs') (by decide)`), and
the genuine `ok`/`fail` interactions on the shared sub-derivation IHs.
-/

namespace Shallot.MacroPeg

/-- Every element that appears in a successful `DerivesArgsPar` derivation
itself has a SUCCESS derivation on the same `input`. Structural (no
determinism needed): each `cons` step literally stores the head's success
`h1`, and the tail is handled by the induction hypothesis. Proved by
induction on the argument list with inversion (`cases`) on the derivation,
so it needs neither the mutual recursor nor `motive_2`. -/
theorem derivesArgsPar_mem_ok {g : MGrammar} {s : Strategy} {input : List Char} :
    ∀ {args vals : List MExp}, DerivesArgsPar g s input args vals →
      ∀ {a : MExp}, a ∈ args → ∃ t r, MDerives g s a input (.ok t r) := by
  intro args
  induction args with
  | nil =>
    intro vals h a ha
    cases ha
  | cons b bs ih =>
    intro vals h a ha
    cases h with
    | cons a' as' input' p rest t vs h1 hp h2 =>
      cases ha with
      | head => exact ⟨t, rest, h1⟩
      | tail _ hmem => exact ih h2 hmem

theorem mderives_det {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char} {o₁ o₂ : MOutcome}
    (h₁ : MDerives g s e x o₁) (h₂ : MDerives g s e x o₂) : o₁ = o₂ := by
  revert h₂
  induction h₁ using MDerives.rec
    (motive_2 := fun input args vals _ =>
      (∀ vals₂, DerivesArgsPar g s input args vals₂ → vals = vals₂) ∧
      (∀ a, a ∈ args → ∀ o, MDerives g s a input o → ∃ t r, o = MOutcome.ok t r))
    generalizing o₂ with
  | eps input =>
    intro h₂
    cases h₂
    rfl
  | anyOk c rest =>
    intro h₂
    cases h₂
    rfl
  | anyFail =>
    intro h₂
    cases h₂
    rfl
  | chrOk c d rest hcd =>
    intro h₂
    cases h₂ with
    | chrOk _ _ _ _ => rfl
    | chrFail _ _ _ h' => rw [hcd] at h'; exact Bool.noConfusion h'
  | chrFail c d rest hcd =>
    intro h₂
    cases h₂ with
    | chrOk _ _ _ h' => rw [hcd] at h'; exact Bool.noConfusion h'
    | chrFail _ _ _ _ => rfl
  | chrEmpty c =>
    intro h₂
    cases h₂
    rfl
  | rangeOk lo hi d rest hcond =>
    intro h₂
    cases h₂ with
    | rangeOk _ _ _ _ _ => rfl
    | rangeFail _ _ _ _ h' => rw [hcond] at h'; exact Bool.noConfusion h'
  | rangeFail lo hi d rest hcond =>
    intro h₂
    cases h₂ with
    | rangeOk _ _ _ _ h' => rw [hcond] at h'; exact Bool.noConfusion h'
    | rangeFail _ _ _ _ _ => rfl
  | rangeEmpty lo hi =>
    intro h₂
    cases h₂
    rfl
  | litOk str input rest hs =>
    intro h₂
    cases h₂ with
    | litOk _ _ rest' h' =>
      rw [hs] at h'
      injection h' with hrest
      subst hrest
      rfl
    | litFail _ _ h' =>
      rw [hs] at h'
      injection h'
  | litFail str input hs =>
    intro h₂
    cases h₂ with
    | litOk _ _ rest' h' =>
      rw [hs] at h'
      injection h'
    | litFail _ _ _ => rfl
  | dbg e input =>
    intro h₂
    cases h₂ with
    | dbg _ _ => rfl
  | paramFail k input =>
    intro h₂
    cases h₂ with
    | paramFail _ _ => rfl
  | callNameOk i args r input rest t hs hr ha hd ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | callNameFail _ _ r' _ hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParArgFail _ _ _ _ _ _ _ hs' _ _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callMissing _ _ _ hr' =>
      rw [hr] at hr'
      injection hr'
    | callArity _ _ r' _ hr' ha' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha ha'
  | callNameFail i args r input hs hr ha hd ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  | callParOk i args r input rest vals t hs hr ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3
    | callParArgFail _ pre badArg post r' _ preVals hs' hr' ha' hpre' hfail' =>
      have hmem2 : badArg ∈ pre ++ badArg :: post := by simp
      obtain ⟨t0, r0, hc⟩ := ihargs.2 badArg hmem2 .fail hfail'
      injection hc
    | callMissing _ _ _ hr' =>
      rw [hr] at hr'
      injection hr'
    | callArity _ _ r' _ hr' ha' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha ha'
  | callParFail i args r input vals hs hr ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  | callParArgFail i pre badArg post r input preVals hs hr ha hpre hfail ihpre ih =>
    intro h₂
    -- `.call`'s argument list is the structured `pre ++ badArg :: post`, on
    -- which `cases h₂` cannot solve the append-index equation for the
    -- `callParArgFail`-vs-`callParArgFail` sub-goal; generalize it to a plain
    -- variable first so dependent elimination succeeds for every constructor.
    generalize hargeq : pre ++ badArg :: post = args at h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      have hmem0 : badArg ∈ pre ++ badArg :: post := by simp
      rw [hargeq] at hmem0
      obtain ⟨t0, r0, hok⟩ := derivesArgsPar_mem_ok hargs' hmem0
      have h3 := ih hok
      injection h3
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  | callMissing i args input hr =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr'
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr'
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  | callArity i args r input hr ha =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha' ha
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha' ha
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ hd₁ hd₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | seqOk _ _ _ rest₁' rest₂' t₁' t₂' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4 with ht' hrest'
      subst ht'
      subst hrest'
      rfl
    | seqFail₁ _ _ _ hd₁' =>
      have h3 := ih₁ hd₁'
      injection h3
    | seqFail₂ _ _ _ rest₁' t₁' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4
  | seqFail₁ e₁ e₂ input hd₁ ih₁ =>
    intro h₂
    cases h₂ with
    | seqOk _ _ _ rest₁' rest₂' t₁' t₂' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3
    | seqFail₁ _ _ _ _ => rfl
    | seqFail₂ _ _ _ rest₁' t₁' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3
  | seqFail₂ e₁ e₂ input rest₁ t₁ hd₁ hd₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | seqOk _ _ _ rest₁' rest₂' t₁' t₂' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4
    | seqFail₁ _ _ _ hd₁' =>
      have h3 := ih₁ hd₁'
      injection h3
    | seqFail₂ _ _ _ rest₁' t₁' hd₁' hd₂' => rfl
  | altL e₁ e₂ input rest t hd ih =>
    intro h₂
    cases h₂ with
    | altL _ _ _ rest' t' hd' =>
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | altR _ _ _ rest' t' hf' hok' =>
      have h3 := ih hf'
      injection h3
    | altFail _ _ _ hf₁' hf₂' =>
      have h3 := ih hf₁'
      injection h3
  | altR e₁ e₂ input rest t hf hok ihf ihok =>
    intro h₂
    cases h₂ with
    | altL _ _ _ rest' t' hd' =>
      have h3 := ihf hd'
      injection h3
    | altR _ _ _ rest' t' hf' hok' =>
      have h3 := ihok hok'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | altFail _ _ _ hf₁' hf₂' =>
      have h3 := ihok hf₂'
      injection h3
  | altFail e₁ e₂ input hf₁ hf₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | altL _ _ _ rest' t' hd' =>
      have h3 := ih₁ hd'
      injection h3
    | altR _ _ _ rest' t' hf' hok' =>
      have h3 := ih₂ hok'
      injection h3
    | altFail _ _ _ _ _ => rfl
  | starNil e input hf ih =>
    intro h₂
    cases h₂ with
    | starNil _ _ _ => rfl
    | starCons _ _ rest₁' rest₂' t' ts' hd₁' hd₂' =>
      have h3 := ih hd₁'
      injection h3
  | starCons e input rest rest' t ts hd₁ hd₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | starNil _ _ hf' =>
      have h3 := ih₁ hf'
      injection h3
    | starCons _ _ rest₁' rest₂' t' ts' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4 with hts hrest'
      subst hts
      subst hrest'
      rfl
  | notOk e input rest t hd ih =>
    intro h₂
    cases h₂ with
    | notOk _ _ rest' t' hd' => rfl
    | notFail _ _ hf' =>
      have h3 := ih hf'
      injection h3
  | notFail e input hf ih =>
    intro h₂
    cases h₂ with
    | notOk _ _ rest' t' hd' =>
      have h3 := ih hd'
      injection h3
    | notFail _ _ _ => rfl
  | nil input =>
    refine ⟨?_, ?_⟩
    · intro vals₂ h
      cases h
      rfl
    · intro a ha
      cases ha
  | cons a as input p rest t vs h1 hp h2 ih1 ih2 =>
    refine ⟨?_, ?_⟩
    · intro vals₂ h
      cases h with
      | cons a' as' input' p' rest' t' vs' h1' hp' h2' =>
        have h3 := ih1 h1'
        injection h3 with _ hrest
        subst hrest
        have hpp : p ++ rest = p' ++ rest := by rw [← hp, ← hp']
        have hpeq := List.append_cancel_right hpp
        have hvv := ih2.1 vs' h2'
        rw [hpeq, hvv]
    · intro a0 ha0
      cases ha0 with
      | head => intro o hd0; exact ⟨t, rest, (ih1 hd0).symm⟩
      | tail _ hmem => exact ih2.2 a0 hmem

end Shallot.MacroPeg
