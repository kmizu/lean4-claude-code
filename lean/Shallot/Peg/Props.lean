import Shallot.Peg.Semantics

/-!
# P1 — the suffix invariant

A successful derivation consumes a prefix: `Derives g e x (.ok t r)` implies
`∃ p, x = p ++ r`. Groundwork for the roundtrip stack (M11), where printed
text is consumed exactly.
-/

namespace Shallot

theorem stripPrefix?_suffix :
    ∀ (s input rest : List Char), stripPrefix? s input = some rest →
      ∃ p, input = p ++ rest := by
  intro s
  induction s with
  | nil =>
    intro input rest h
    simp [stripPrefix?] at h
    exact ⟨[], by simp [h]⟩
  | cons c cs ih =>
    intro input rest h
    cases input with
    | nil => simp [stripPrefix?] at h
    | cons d ds =>
      simp only [stripPrefix?] at h
      split at h
      · obtain ⟨p, hp⟩ := ih ds rest h
        exact ⟨d :: p, by simp [hp]⟩
      · exact absurd h (by simp)

theorem derives_suffix {g : Grammar} {e : PExp} {x : List Char} {o : Outcome}
    (h : Derives g e x o) :
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
  | ntOk i e input rest t hr hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  | ntFail _ _ _ _ _ => intro _ _ ho; cases ho
  | ntMissing _ _ _ => intro _ _ ho; cases ho
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

end Shallot
