import Shallot.Peg.Interp

/-!
# T0 — fuel monotonicity

`pegRun g f e x = some o → pegRun g (f+1) e x = some o`, plus the `≤`
corollary. Everything downstream (soundness bookkeeping, completeness fuel
assembly with `max + 1`) leans on this.

Proof-engineering note: `simp only [pegRun]` must NOT be used to unfold the
goal — the goal's inner recursive calls sit at fuel `f+1`, which matches the
successor equation, so simp expands them recursively and the IH rewrite
target disappears. `rw [pegRun]` unfolds exactly one layer.
-/

namespace Shallot

theorem pegRun_mono {g : Grammar} {f : Nat} {e : PExp} {x : List Char} {o : Outcome}
    (h : pegRun g f e x = some o) : pegRun g (f + 1) e x = some o := by
  induction f generalizing e x o with
  | zero => simp [pegRun] at h
  | succ f ih =>
    rw [pegRun.eq_def] at h ⊢
    dsimp only at h ⊢
    cases e with
    | eps => exact h
    | any => cases x <;> exact h
    | chr c =>
      cases x with
      | nil => exact h
      | cons d rest =>
        dsimp only at h ⊢
        split at h <;> simp_all
    | range lo hi =>
      cases x with
      | nil => exact h
      | cons d rest =>
        dsimp only at h ⊢
        split at h <;> simp_all
    | lit s =>
      dsimp only at h ⊢
      split at h <;> simp_all
    | nt i =>
      dsimp only at h ⊢
      cases hr : ruleAt g.rules i with
      | none => rw [hr] at h; exact h
      | some e' =>
        rw [hr] at h
        dsimp only at h ⊢
        cases h1 : pegRun g f e' x with
        | none => rw [h1] at h; exact absurd h (by simp)
        | some o1 =>
          rw [h1] at h
          rw [ih h1]
          exact h
    | seq e₁ e₂ =>
      dsimp only at h ⊢
      cases h1 : pegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | fail => exact h
        | ok t r =>
          dsimp only at h ⊢
          cases h2 : pegRun g f e₂ r with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | alt e₁ e₂ =>
      dsimp only at h ⊢
      cases h1 : pegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | ok t r => exact h
        | fail =>
          dsimp only at h ⊢
          cases h2 : pegRun g f e₂ x with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | star e =>
      dsimp only at h ⊢
      cases h1 : pegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | fail => exact h
        | ok t r =>
          dsimp only at h ⊢
          cases h2 : pegRun g f (.star e) r with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | notP e =>
      dsimp only at h ⊢
      cases h1 : pegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | ok t r => exact h
        | fail => exact h

theorem pegRun_mono_le {g : Grammar} {f f' : Nat} {e : PExp} {x : List Char} {o : Outcome}
    (hle : f ≤ f') (h : pegRun g f e x = some o) : pegRun g f' e x = some o := by
  induction hle with
  | refl => exact h
  | step _ ih => exact pegRun_mono ih

end Shallot
