import MacroPeg.Interp

/-!
# T0 — fuel monotonicity (Macro PEG, call-by-name + call-by-value-par)

`mpegRun g s f e x = some o → mpegRun g s (f+1) e x = some o`, plus the `≤`
corollary. The `.callByValuePar` case of `.call` needs a companion fact
about `evalArgsPar` — `evalArgsPar_mono_of_mpegRun_mono` below — but this
does NOT require a genuinely mutual (simultaneous) induction: `evalArgsPar`
recurses on the ARGUMENT LIST, not on fuel (its own fuel parameter is held
fixed and only threaded down into each `mpegRun` sub-call), so "if
`mpegRun` is mono AT A GIVEN FUEL LEVEL, so is `evalArgsPar` at that same
level" is provable by plain list induction, taking mono-at-that-level as a
hypothesis. And that hypothesis is exactly what `mpegRun_mono`'s own
`induction f ... with | succ f ih => ...` already hands you as `ih` — `ih`
IS "mono at fuel f", which is precisely what's needed to relate the
`.call`/`.callByValuePar` branch's `evalArgsPar g s f ...` (inner fuel `f`,
from unfolding `mpegRun` at `f+1`) to `evalArgsPar g s (f+1) ...` (inner
fuel `f+1`, from unfolding `mpegRun` at `f+2`). So the two lemmas compose
in strictly one direction: prove `evalArgsPar_mono_of_mpegRun_mono` first
(ordinary list induction, `mpegRun`-mono taken as a parameter), then use it
as a black box inside `mpegRun_mono`'s own fuel induction.

Proof-engineering note (same discipline as the M-PEG `pegRun`/`mpegRun`
proofs before it): `simp only [mpegRun]`/`simp only [evalArgsPar]` must NOT
be used to unfold a goal holding successor-fuel calls — `rw [X.eq_def]` +
`dsimp only` unfolds exactly one layer.
-/

namespace Shallot.MacroPeg

/-- If `mpegRun` is monotonic at fuel level `f` (the exact fact `mpegRun_mono`'s
own induction hands you as `ih`), then so is `evalArgsPar` at that same
level. Plain structural induction on the argument list — no fuel induction
needed here at all. -/
theorem evalArgsPar_mono_of_mpegRun_mono {g : MGrammar} {s : Strategy} {f : Nat}
    (hM : ∀ {e : MExp} {x : List Char} {o : MOutcome},
      mpegRun g s f e x = some o → mpegRun g s (f + 1) e x = some o) :
    ∀ {input : List Char} {args : List MExp} {r : Option (List MExp)},
      evalArgsPar g s f input args = some r → evalArgsPar g s (f + 1) input args = some r := by
  intro input args
  induction args with
  | nil => intro r h; simp only [evalArgsPar] at h ⊢; exact h
  | cons a as ih =>
    intro r h
    rw [evalArgsPar.eq_def] at h ⊢
    dsimp only at h ⊢
    cases h1 : mpegRun g s f a input with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some o1 =>
      rw [h1] at h
      rw [hM h1]
      cases o1 with
      | fail => exact h
      | ok t rest =>
        dsimp only at h ⊢
        cases h2 : evalArgsPar g s f input as with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some o2 =>
          rw [h2] at h
          rw [ih h2]
          exact h

theorem mpegRun_mono {g : MGrammar} {s : Strategy} {f : Nat} {e : MExp} {x : List Char} {o : MOutcome}
    (h : mpegRun g s f e x = some o) : mpegRun g s (f + 1) e x = some o := by
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
    | lit str =>
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
        by_cases hbeq : (r.arity == args.length) = true
        · simp only [if_pos hbeq] at h ⊢
          cases s with
          | callByName =>
            dsimp only at h ⊢
            cases h1 : mpegRun g .callByName f (MExp.subst args r.body) x with
            | none => rw [h1] at h; exact absurd h (by simp)
            | some o1 =>
              rw [h1] at h
              rw [ih h1]
              exact h
          | callByValuePar =>
            dsimp only at h ⊢
            cases h1 : evalArgsPar g .callByValuePar f x args with
            | none => rw [h1] at h; exact absurd h (by simp)
            | some o1 =>
              rw [h1] at h
              rw [evalArgsPar_mono_of_mpegRun_mono (@ih) h1]
              cases o1 with
              | none => exact h
              | some vals =>
                dsimp only at h ⊢
                cases h2 : mpegRun g .callByValuePar f (MExp.subst vals r.body) x with
                | none => rw [h2] at h; exact absurd h (by simp)
                | some o2 =>
                  rw [h2] at h
                  rw [ih h2]
                  exact h
        · simp only [if_neg hbeq] at h ⊢
          exact h
    | seq e₁ e₂ =>
      dsimp only at h ⊢
      cases h1 : mpegRun g s f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | fail => exact h
        | ok t r =>
          dsimp only at h ⊢
          cases h2 : mpegRun g s f e₂ r with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | alt e₁ e₂ =>
      dsimp only at h ⊢
      cases h1 : mpegRun g s f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | ok t r => exact h
        | fail =>
          dsimp only at h ⊢
          cases h2 : mpegRun g s f e₂ x with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | star e =>
      dsimp only at h ⊢
      cases h1 : mpegRun g s f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | fail => exact h
        | ok t r =>
          dsimp only at h ⊢
          cases h2 : mpegRun g s f (.star e) r with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            rw [ih h2]
            exact h
    | notP e =>
      dsimp only at h ⊢
      cases h1 : mpegRun g s f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        rw [ih h1]
        cases o1 with
        | ok t r => exact h
        | fail => exact h
    | dbg e => exact h

theorem mpegRun_mono_le {g : MGrammar} {s : Strategy} {f f' : Nat} {e : MExp} {x : List Char} {o : MOutcome}
    (hle : f ≤ f') (h : mpegRun g s f e x = some o) : mpegRun g s f' e x = some o := by
  induction hle with
  | refl => exact h
  | step _ ih => exact mpegRun_mono ih

end Shallot.MacroPeg
