import MacroPeg.Semantics

/-!
# Determinism of the macro-PEG derivation relation

`MDerives g e x o₁ → MDerives g e x o₂ → o₁ = o₂`. The T2 analogue for
`Shallot.MacroPeg` — a verbatim mirror of `Shallot.derives_det`, extended
with the macro-specific constructors.

Proof: induction on the first derivation (generalizing the second
outcome), then case analysis on the second derivation in every branch.
The base-PEG constructors are a rule-for-rule transcription of
`derives_det`. The new cases:

- `dbg` / `paramFail`: exactly one constructor concludes at `.dbg e` /
  `.param k`, so `cases h₂` leaves a single, `rfl`-closeable goal.
- `callOk` / `callFail` / `callMissing` / `callArity`: all four conclude
  at the `.call i args` LHS, so each of the four top-level cases must
  cross-case on all four possibilities. Rule-lookup clashes die on
  `ruleAtM g.rules i` (`rw [hr] at hr'; injection hr'`, mirroring
  `ntOk`/`ntMissing`), arity clashes die on `r.arity = args.length`
  vs `r.arity ≠ args.length` (`absurd`), and the genuine `callOk`/`callFail`
  interaction is resolved by the induction hypothesis on the shared
  `MExp.subst args r.body` sub-derivation (mirroring `ntOk`/`ntFail`).
-/

namespace Shallot.MacroPeg

theorem mderives_det {g : MGrammar} {e : MExp} {x : List Char} {o₁ o₂ : MOutcome}
    (h₁ : MDerives g e x o₁) (h₂ : MDerives g e x o₂) : o₁ = o₂ := by
  revert h₂
  induction h₁ generalizing o₂ with
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
  | litOk s input rest hs =>
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
  | litFail s input hs =>
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
  | callOk i args r input rest t hr ha hd ih =>
    intro h₂
    cases h₂ with
    | callOk _ _ r' _ rest' t' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | callFail _ _ r' _ hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | callMissing _ _ _ hr' =>
      rw [hr] at hr'
      injection hr'
    | callArity _ _ r' _ hr' ha' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha ha'
  | callFail i args r input hr ha hd ih =>
    intro h₂
    cases h₂ with
    | callOk _ _ r' _ rest' t' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | callFail _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ _ => rfl
    | callArity _ _ _ _ _ _ => rfl
  | callMissing i args input hr =>
    intro h₂
    cases h₂ with
    | callOk _ _ r' _ rest' t' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr'
    | callFail _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ _ => rfl
    | callArity _ _ _ _ _ _ => rfl
  | callArity i args r input hr ha =>
    intro h₂
    cases h₂ with
    | callOk _ _ r' _ rest' t' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha' ha
    | callFail _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ _ => rfl
    | callArity _ _ _ _ _ _ => rfl
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

end Shallot.MacroPeg
