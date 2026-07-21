import MacroPeg.Interp

/-!
# T0 — fuel monotonicity (Macro PEG)

`mpegRun g f e x = some o → mpegRun g (f+1) e x = some o`, plus the `≤`
corollary. Verbatim transcription of `Shallot.Peg.Fuel.pegRun_mono`, with
`.call` playing `.nt`'s role (one extra `if` for the arity check) and two
new one-line leaf cases (`.param`, `.dbg`) that don't touch fuel at all.

Proof-engineering note (same discipline as `Shallot/Peg/Fuel.lean`):
`simp only [mpegRun]` must NOT be used to unfold the goal — the goal's inner
recursive calls sit at fuel `f+1`, matching the successor equation, so simp
expands them recursively and the IH rewrite target disappears. `rw
[mpegRun.eq_def]` unfolds exactly one layer.
-/

namespace Shallot.MacroPeg

theorem mpegRun_mono {g : MGrammar} {f : Nat} {e : MExp} {x : List Char} {o : MOutcome}
    (h : mpegRun g f e x = some o) : mpegRun g (f + 1) e x = some o := by
  induction f generalizing e x o with
  | zero => simp [mpegRun] at h
  | succ f ih =>
    rw [mpegRun.eq_def] at h ⊢
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
    | param k => exact h
    | call i args =>
      dsimp only at h ⊢
      cases hr : ruleAtM g.rules i with
      | none => rw [hr] at h; exact h
      | some r =>
        rw [hr] at h
        dsimp only at h ⊢
        cases hbeq : r.arity == args.length with
        | false => simp only [hbeq] at h ⊢; exact h
        | true =>
          simp only [hbeq] at h ⊢
          cases h1 : mpegRun g f (MExp.subst args r.body) x with
          | none => rw [h1] at h; exact absurd h (by simp)
          | some o1 =>
            rw [h1] at h
            rw [ih h1]
            exact h
    | seq e₁ e₂ =>
      dsimp only at h ⊢
      cases h1 : mpegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | fail => exact h
        | ok t r =>
          dsimp only at h ⊢
          cases h2 : mpegRun g f e₂ r with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | alt e₁ e₂ =>
      dsimp only at h ⊢
      cases h1 : mpegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | ok t r => exact h
        | fail =>
          dsimp only at h ⊢
          cases h2 : mpegRun g f e₂ x with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | star e =>
      dsimp only at h ⊢
      cases h1 : mpegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | fail => exact h
        | ok t r =>
          dsimp only at h ⊢
          cases h2 : mpegRun g f (.star e) r with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | notP e =>
      dsimp only at h ⊢
      cases h1 : mpegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | ok t r => exact h
        | fail => exact h
    | dbg e => exact h

theorem mpegRun_mono_le {g : MGrammar} {f f' : Nat} {e : MExp} {x : List Char} {o : MOutcome}
    (hle : f ≤ f') (h : mpegRun g f e x = some o) : mpegRun g f' e x = some o := by
  induction hle with
  | refl => exact h
  | step _ ih => exact mpegRun_mono ih

end Shallot.MacroPeg
