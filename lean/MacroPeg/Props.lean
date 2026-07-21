import MacroPeg.Semantics
import Shallot.Peg.Props

/-!
# P1 (macro-PEG) — the suffix invariant for `MDerives`

The `MDerives` analogue of `Shallot.Peg.Props.derives_suffix`: a successful
macro-PEG derivation consumes a prefix, i.e. `MDerives g e x (.ok t r)`
implies `∃ p, x = p ++ r`. Structure mirrors `derives_suffix` one case per
constructor; the `.lit` case reuses `Shallot.stripPrefix?_suffix` verbatim
(same `stripPrefix?` from `Shallot.Peg.Syntax`).
-/

namespace Shallot.MacroPeg

theorem mderives_suffix {g : MGrammar} {e : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives g e x o) :
    ∀ t r, o = .ok t r → ∃ p, x = p ++ r := by
  induction h with
  | eps input => exact fun t r ho => ⟨[], by cases ho; simp⟩
  | anyOk c rest => exact fun t r ho => ⟨[c], by cases ho; simp⟩
  | anyFail => intro _ _ ho; cases ho
  | chrOk c d rest _ => exact fun t r ho => ⟨[d], by cases ho; simp⟩
  | chrFail _ _ _ _ => intro _ _ ho; cases ho
  | chrEmpty _ => intro _ _ ho; cases ho
  | rangeOk lo hi d rest _ => exact fun t r ho => ⟨[d], by cases ho; simp⟩
  | rangeFail _ _ _ _ _ => intro _ _ ho; cases ho
  | rangeEmpty _ _ => intro _ _ ho; cases ho
  | litOk s input rest hs =>
    intro t r ho
    cases ho
    exact stripPrefix?_suffix s input rest hs
  | litFail _ _ _ => intro _ _ ho; cases ho
  | dbg e input => exact fun t r ho => ⟨[], by cases ho; simp⟩
  | paramFail _ _ => intro _ _ ho; cases ho
  | callOk i args r input rest t hr ha hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  | callFail _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
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

end Shallot.MacroPeg
