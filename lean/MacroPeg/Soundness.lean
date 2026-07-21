import MacroPeg.Semantics
import MacroPeg.Interp

/-!
# T1 — interpreter soundness (Macro PEG)

`mpegRun g f e x = some o → MDerives g e x o`: any outcome the fuel
interpreter actually returns — success or failure alike — is derivable in
the formal semantics (`none` means "out of fuel" and is excluded by the
hypothesis). Verbatim mirror of `Shallot.Peg.Soundness.pegRun_sound`, with
`.nt` becoming `.call` (an extra arity `if`, see `MacroPeg/Fuel.lean`'s
working idiom) and two new leaf cases (`.param`, `.dbg`) with no `Derives`
analogue.

Proof-engineering notes (same discipline as T0 in `Fuel.lean`):
- never `simp only [mpegRun]` on anything holding successor-fuel calls; use
  `rw [mpegRun.eq_def]` then `dsimp only` to unfold exactly one layer
- `cases hr : <expr>` substitutes occurrences in the goal, not in
  hypotheses — always follow with `rw [hr] at h`
- `split at h` alone does not sync the goal; for the `.call` arity `if`,
  `by_cases hpos : r.arity ≠ args.length` + `simp only [if_pos/if_neg]` is
  what works (mirrors `Fuel.lean`)
- the interpreter's inner-star `some .fail` branch is semantically
  unreachable: there the IH yields `MDerives g (.star e) rest .fail`, which
  `mStarNeverFails` refutes
-/

namespace Shallot.MacroPeg

/-- A star never fails: the only `MDerives` rules concluding at a `.star`
expression are `starNil` and `starCons`, and both produce `.ok`. -/
theorem mStarNeverFails {g : MGrammar} {e : MExp} {input : List Char} {o : MOutcome}
    (h : MDerives g (.star e) input o) : o ≠ .fail := by
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
theorem mpegRun_sound {g : MGrammar} {f : Nat} {e : MExp} {x : List Char} {o : MOutcome}
    (h : mpegRun g f e x = some o) : MDerives g e x o := by
  induction f generalizing e x o with
  | zero => simp [mpegRun] at h
  | succ f ih =>
    rw [mpegRun.eq_def] at h
    dsimp only at h
    cases e with
    | eps =>
      dsimp only at h
      cases h
      exact MDerives.eps x
    | any =>
      cases x with
      | nil =>
        dsimp only at h
        cases h
        exact MDerives.anyFail
      | cons c rest =>
        dsimp only at h
        cases h
        exact MDerives.anyOk c rest
    | chr c =>
      cases x with
      | nil =>
        dsimp only at h
        cases h
        exact MDerives.chrEmpty c
      | cons d rest =>
        dsimp only at h
        split at h
        · rename_i hb
          cases h
          exact MDerives.chrOk c d rest hb
        · rename_i hb
          cases h
          exact MDerives.chrFail c d rest (eq_false_of_not_eq_true hb)
    | range lo hi =>
      cases x with
      | nil =>
        dsimp only at h
        cases h
        exact MDerives.rangeEmpty lo hi
      | cons d rest =>
        dsimp only at h
        split at h
        · rename_i hb
          cases h
          exact MDerives.rangeOk lo hi d rest hb
        · rename_i hb
          cases h
          exact MDerives.rangeFail lo hi d rest (eq_false_of_not_eq_true hb)
    | lit s =>
      dsimp only at h
      cases hs : stripPrefix? s x with
      | some rest =>
        rw [hs] at h
        dsimp only at h
        cases h
        exact MDerives.litOk s x rest hs
      | none =>
        rw [hs] at h
        dsimp only at h
        cases h
        exact MDerives.litFail s x hs
    | param k =>
      dsimp only at h
      cases h
      exact MDerives.paramFail k x
    | call i args =>
      dsimp only at h
      cases hr : ruleAtM g.rules i with
      | none =>
        rw [hr] at h
        dsimp only at h
        cases h
        exact MDerives.callMissing i args x hr
      | some r =>
        rw [hr] at h
        dsimp only at h
        by_cases hbeq : (r.arity == args.length) = true
        · simp only [if_pos hbeq] at h
          have ha : r.arity = args.length := by simpa using hbeq
          cases h1 : mpegRun g f (MExp.subst args r.body) x with
          | none => rw [h1] at h; exact absurd h (by simp)
          | some o1 =>
            rw [h1] at h
            cases o1 with
            | fail =>
              dsimp only at h
              cases h
              exact MDerives.callFail i args r x hr ha (ih h1)
            | ok t rest =>
              dsimp only at h
              cases h
              exact MDerives.callOk i args r x rest t hr ha (ih h1)
        · simp only [if_neg hbeq] at h
          cases h
          have hne : r.arity ≠ args.length := by
            intro he
            exact hbeq (by simp [he])
          exact MDerives.callArity i args r x hr hne
    | seq e₁ e₂ =>
      dsimp only at h
      cases h1 : mpegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | fail =>
          dsimp only at h
          cases h
          exact MDerives.seqFail₁ e₁ e₂ x (ih h1)
        | ok t₁ rest₁ =>
          dsimp only at h
          cases h2 : mpegRun g f e₂ rest₁ with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            cases o2 with
            | fail =>
              dsimp only at h
              cases h
              exact MDerives.seqFail₂ e₁ e₂ x rest₁ t₁ (ih h1) (ih h2)
            | ok t₂ rest₂ =>
              dsimp only at h
              cases h
              exact MDerives.seqOk e₁ e₂ x rest₁ rest₂ t₁ t₂ (ih h1) (ih h2)
    | alt e₁ e₂ =>
      dsimp only at h
      cases h1 : mpegRun g f e₁ x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | ok t rest =>
          dsimp only at h
          cases h
          exact MDerives.altL e₁ e₂ x rest t (ih h1)
        | fail =>
          dsimp only at h
          cases h2 : mpegRun g f e₂ x with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            cases o2 with
            | ok t rest =>
              dsimp only at h
              cases h
              exact MDerives.altR e₁ e₂ x rest t (ih h1) (ih h2)
            | fail =>
              dsimp only at h
              cases h
              exact MDerives.altFail e₁ e₂ x (ih h1) (ih h2)
    | star e =>
      dsimp only at h
      cases h1 : mpegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | fail =>
          dsimp only at h
          cases h
          exact MDerives.starNil e x (ih h1)
        | ok t rest =>
          dsimp only at h
          cases h2 : mpegRun g f (.star e) rest with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some o2 =>
            rw [h2] at h
            cases o2 with
            | fail =>
              -- semantically unreachable: a star never fails
              exact absurd rfl (mStarNeverFails (ih h2))
            | ok ts rest' =>
              dsimp only at h
              cases h
              exact MDerives.starCons e x rest rest' t ts (ih h1) (ih h2)
    | notP e =>
      dsimp only at h
      cases h1 : mpegRun g f e x with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some o1 =>
        rw [h1] at h
        cases o1 with
        | ok t rest =>
          dsimp only at h
          cases h
          exact MDerives.notOk e x rest t (ih h1)
        | fail =>
          dsimp only at h
          cases h
          exact MDerives.notFail e x (ih h1)
    | dbg e =>
      dsimp only at h
      cases h
      exact MDerives.dbg e x

end Shallot.MacroPeg
