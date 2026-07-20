import Shallot.Peg.Semantics

/-!
# Determinism of the PEG derivation relation

`Derives g e x o₁ → Derives g e x o₂ → o₁ = o₂`. Since `Outcome.ok`
carries the parse tree, this gives parse-tree uniqueness for free.

Proof: induction on the first derivation (generalizing the second
outcome), then case analysis on the second derivation in every branch.
Conflicting pairs die on Bool side-condition contradictions
(`beqChar`/`leChar`) or `Option`-result mismatches (`ruleAt`,
`stripPrefix?`); the genuinely interactive pairs (`altL` vs
`altR`/`altFail`, `starNil` vs `starCons`, `seqOk` vs `seqFail₂`,
`notOk` vs `notFail`) are resolved by the induction hypotheses on the
shared sub-derivations, which yield `Outcome`-constructor clashes.
-/

namespace Shallot

theorem derives_det {g : Grammar} {e : PExp} {x : List Char} {o₁ o₂ : Outcome}
    (h₁ : Derives g e x o₁) (h₂ : Derives g e x o₂) : o₁ = o₂ := by
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
  | ntOk i e input rest t hr hd ih =>
    intro h₂
    cases h₂ with
    | ntOk _ e' _ rest' t' hr' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | ntFail _ e' _ hr' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | ntMissing _ _ hr' =>
      rw [hr] at hr'
      injection hr'
  | ntFail i e input hr hd ih =>
    intro h₂
    cases h₂ with
    | ntOk _ e' _ rest' t' hr' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | ntFail _ e' _ hr' hd' => rfl
    | ntMissing _ _ _ => rfl
  | ntMissing i input hr =>
    intro h₂
    cases h₂ with
    | ntOk _ e' _ rest' t' hr' hd' =>
      rw [hr] at hr'
      injection hr'
    | ntFail _ e' _ hr' hd' => rfl
    | ntMissing _ _ _ => rfl
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

end Shallot
