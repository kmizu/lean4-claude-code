import Shallot.Peg.Semantics
import Shallot.Peg.Interp

/-!
# T1 — interpreter soundness

`pegRun g f e x = some o → Derives g e x o`: any outcome the fuel
interpreter actually returns — success or failure alike — is derivable in
the formal semantics (`none` means "out of fuel" and is excluded by the
hypothesis).

Proof-engineering notes (same discipline as T0 in `Fuel.lean`):
- never `simp only [pegRun]` on anything holding successor-fuel calls; use
  `rw [pegRun.eq_def]` then `dsimp only` to unfold exactly one layer
- `cases hr : <expr>` substitutes occurrences in the goal, not in
  hypotheses — always follow with `rw [hr] at h`
- the interpreter's inner-star `some .fail` branch is semantically
  unreachable: there the IH yields `Derives g (.star e) rest .fail`, which
  `starNeverFails` refutes
-/

namespace Shallot

/-- A star never fails: the only `Derives` rules concluding at a `.star`
expression are `starNil` and `starCons`, and both produce `.ok`. -/
theorem starNeverFails {g : Grammar} {e : PExp} {input : List Char} {o : Outcome}
    (h : Derives g (.star e) input o) : o ≠ .fail := by
  intro hf
  subst hf
  cases h

/-- Local Bool inversion helper: `¬(b = true)` gives `b = false` (used for
the `if` side conditions of `chr`/`range`; kept local so the proof does not
lean on stdlib lemma names). -/
theorem eq_false_of_not_eq_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

/-- T1 — soundness: whatever the interpreter returns is derivable. -/
theorem pegRun_sound {g : Grammar} {f : Nat} {e : PExp} {x : List Char} {o : Outcome}
    (h : pegRun g f e x = some o) : Derives g e x o := by
  induction f generalizing e x o with
  | zero => simp [pegRun] at h
  | succ f ih =>
    rw [pegRun.eq_def] at h
    dsimp only at h
    cases e with
    | eps =>
      dsimp only at h
      cases h
      exact Derives.eps x
    | any =>
      cases x with
      | nil =>
        dsimp only at h
        cases h
        exact Derives.anyFail
      | cons c rest =>
        dsimp only at h
        cases h
        exact Derives.anyOk c rest
    | chr c =>
      cases x with
      | nil =>
        dsimp only at h
        cases h
        exact Derives.chrEmpty c
      | cons d rest =>
        dsimp only at h
        split at h
        · rename_i hb
          cases h
          exact Derives.chrOk c d rest hb
        · rename_i hb
          cases h
          exact Derives.chrFail c d rest (eq_false_of_not_eq_true hb)
    | range lo hi =>
      cases x with
      | nil =>
        dsimp only at h
        cases h
        exact Derives.rangeEmpty lo hi
      | cons d rest =>
        dsimp only at h
        split at h
        · rename_i hb
          cases h
          exact Derives.rangeOk lo hi d rest hb
        · rename_i hb
          cases h
          exact Derives.rangeFail lo hi d rest (eq_false_of_not_eq_true hb)
    | lit s =>
      dsimp only at h
      cases hs : stripPrefix? s x with
      | some rest =>
        rw [hs] at h
        dsimp only at h
        cases h
        exact Derives.litOk s x rest hs
      | none =>
        rw [hs] at h
        dsimp only at h
        cases h
        exact Derives.litFail s x hs
    | nt i =>
      dsimp only at h
      cases hr : ruleAt g.rules i with
      | none =>
        rw [hr] at h
        dsimp only at h
        cases h
        exact Derives.ntMissing i x hr
      | some e' =>
        rw [hr] at h
        dsimp only at h
        cases h1 : pegRun g f e' x with
        | none => rw [h1] at h; exact absurd h (by simp)
        | some o1 =>
          rw [h1] at h
          cases o1 with
          | fail =>
            dsimp only at h
            cases h
            exact Derives.ntFail i e' x hr (ih h1)
          | ok t rest =>
            dsimp only at h
            cases h
            exact Derives.ntOk i e' x rest t hr (ih h1)
    | seq e₁ e₂ =>
      dsimp only at h
      cases h1 : pegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | fail =>
          dsimp only at h
          cases h
          exact Derives.seqFail₁ e₁ e₂ x (ih h1)
        | ok t₁ rest₁ =>
          dsimp only at h
          cases h2 : pegRun g f e₂ rest₁ with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            cases o2 with
            | fail =>
              dsimp only at h
              cases h
              exact Derives.seqFail₂ e₁ e₂ x rest₁ t₁ (ih h1) (ih h2)
            | ok t₂ rest₂ =>
              dsimp only at h
              cases h
              exact Derives.seqOk e₁ e₂ x rest₁ rest₂ t₁ t₂ (ih h1) (ih h2)
    | alt e₁ e₂ =>
      dsimp only at h
      cases h1 : pegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | ok t rest =>
          dsimp only at h
          cases h
          exact Derives.altL e₁ e₂ x rest t (ih h1)
        | fail =>
          dsimp only at h
          cases h2 : pegRun g f e₂ x with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            cases o2 with
            | ok t rest =>
              dsimp only at h
              cases h
              exact Derives.altR e₁ e₂ x rest t (ih h1) (ih h2)
            | fail =>
              dsimp only at h
              cases h
              exact Derives.altFail e₁ e₂ x (ih h1) (ih h2)
    | star e =>
      dsimp only at h
      cases h1 : pegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | fail =>
          dsimp only at h
          cases h
          exact Derives.starNil e x (ih h1)
        | ok t rest =>
          dsimp only at h
          cases h2 : pegRun g f (.star e) rest with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            cases o2 with
            | fail =>
              -- semantically unreachable: a star never fails
              exact absurd rfl (starNeverFails (ih h2))
            | ok ts rest' =>
              dsimp only at h
              cases h
              exact Derives.starCons e x rest rest' t ts (ih h1) (ih h2)
    | notP e =>
      dsimp only at h
      cases h1 : pegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | ok t rest =>
          dsimp only at h
          cases h
          exact Derives.notOk e x rest t (ih h1)
        | fail =>
          dsimp only at h
          cases h
          exact Derives.notFail e x (ih h1)

end Shallot
