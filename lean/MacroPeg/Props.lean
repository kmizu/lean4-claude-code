import MacroPeg.Semantics
import Shallot.Peg.Props

/-!
# P1 (macro-PEG) — the suffix invariant for `MDerives`

The `MDerives` analogue of `Shallot.Peg.Props.derives_suffix`: a successful
macro-PEG derivation consumes a prefix, i.e. `MDerives g s e x (.ok t r)`
implies `∃ p, x = p ++ r`. Retrofitted from M-PEG's `CallByName`-only
version with `s` threaded through; the new `.callByValuePar` cases
(`callParOk`/`callParFail`/`callParArgFail`) all reduce to the SAME
argument as `callNameOk`/`callNameFail`/etc. — the consumption fact comes
from the sub-derivation `hd`/`hfail` against the SAME `input` the `.call`
itself was run on, so the `hargs : DerivesArgsPar ...` premise (which does
NOT itself constrain `input`/`rest` the way P1 needs) is simply unused in
every case here.
-/

namespace Shallot.MacroPeg

theorem mderives_suffix {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives g s e x o) :
    ∀ t r, o = .ok t r → ∃ p, x = p ++ r := by
  induction h using MDerives.rec (motive_2 := fun _ _ _ _ => True) with
  | eps input => exact fun t r ho => ⟨[], by cases ho; simp⟩
  | anyOk c rest => exact fun t r ho => ⟨[c], by cases ho; simp⟩
  | anyFail => intro _ _ ho; cases ho
  | chrOk c d rest _ => exact fun t r ho => ⟨[d], by cases ho; simp⟩
  | chrFail _ _ _ _ => intro _ _ ho; cases ho
  | chrEmpty _ => intro _ _ ho; cases ho
  | rangeOk lo hi d rest _ => exact fun t r ho => ⟨[d], by cases ho; simp⟩
  | rangeFail _ _ _ _ _ => intro _ _ ho; cases ho
  | rangeEmpty _ _ => intro _ _ ho; cases ho
  | litOk str input rest hs =>
    intro t r ho
    cases ho
    exact stripPrefix?_suffix str input rest hs
  | litFail _ _ _ => intro _ _ ho; cases ho
  | dbg e input => exact fun t r ho => ⟨[], by cases ho; simp⟩
  | paramFail _ _ => intro _ _ ho; cases ho
  | callNameOk i args r input rest t hs hr ha hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  | callNameFail _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  | callParOk i args r input rest vals t hs hr ha hargs ihargs hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  | callParFail _ _ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  | callParArgFail _ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  | callMissing _ _ _ _ => intro _ _ ho; cases ho
  | callArity _ _ _ _ _ _ => intro _ _ ho; cases ho
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro t r ho
    cases ho
    obtain ⟨p₁, hp₁⟩ := ih₁ t₁ rest₁ rfl
    obtain ⟨p₂, hp₂⟩ := ih₂ t₂ rest₂ rfl
    exact ⟨p₁ ++ p₂, by simp [hp₁, hp₂]⟩
  | seqFail₁ _ _ _ _ _ => intro _ _ ho; cases ho
  | seqFail₂ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  | altL e₁ e₂ input rest t hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  | altR e₁ e₂ input rest t h₁ h₂ _ ih₂ =>
    intro t' r' ho
    cases ho
    exact ih₂ t rest rfl
  | altFail _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  | starNil e input _ _ => exact fun t r ho => ⟨[], by cases ho; simp⟩
  | starCons e input rest rest' t ts h₁ h₂ ih₁ ih₂ =>
    intro t' r' ho
    cases ho
    obtain ⟨p₁, hp₁⟩ := ih₁ t rest rfl
    obtain ⟨p₂, hp₂⟩ := ih₂ ts rest' rfl
    exact ⟨p₁ ++ p₂, by simp [hp₁, hp₂]⟩
  | notOk _ _ _ _ _ => intro _ _ ho; cases ho
  | notFail e input _ => exact fun t r ho => ⟨[], by cases ho; simp⟩
  | nil input => trivial
  | cons a as input p rest t vs h1 hp h2 ih => trivial

end Shallot.MacroPeg
