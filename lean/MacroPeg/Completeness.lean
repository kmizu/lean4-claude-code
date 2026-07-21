import MacroPeg.Semantics
import MacroPeg.Fuel

/-!
# T3 — completeness relative to derivation existence (Macro PEG)

The `MacroPeg` analogue of `Shallot.pegRun_complete`: if the formal semantics
`MDerives` derives outcome `o` for `e` on `x`, then some fuel level makes the
interpreter `mpegRun` return `some o`.

Proof: induction on the derivation, mirroring `Shallot/Peg/Completeness.lean`
rule-for-rule for the shared constructors. Leaf rules take fuel `1` and
compute; each recursive rule takes the fuel witnesses of its sub-derivations,
lifts them to their `max` via `mpegRun_mono_le` (T0), and adds one for the
outer layer.

New/changed cases relative to the base PEG proof:
- `dbg`/`paramFail`: unconditional leaves (fuel `1`).
- `callOk`/`callFail`: play `ntOk`/`ntFail`'s role, with the extra arity `if`
  discharged by the `by_cases hpos : r.arity ≠ args.length` idiom from
  `MacroPeg/Fuel.lean` (`ha : r.arity = args.length` contradicts `hpos`).
- `callMissing`/`callArity`: explicit-failure leaves (fuel `1`), mirroring
  `ntMissing`.
-/

namespace Shallot.MacroPeg

theorem mpegRun_complete {g : MGrammar} {e : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives g e x o) : ∃ f, mpegRun g f e x = some o := by
  induction h with
  | eps input =>
    exact ⟨1, by simp [mpegRun]⟩
  | anyOk c rest =>
    exact ⟨1, by simp [mpegRun]⟩
  | anyFail =>
    exact ⟨1, by simp [mpegRun]⟩
  | chrOk c d rest hcd =>
    exact ⟨1, by simp [mpegRun, hcd]⟩
  | chrFail c d rest hcd =>
    exact ⟨1, by simp [mpegRun, hcd]⟩
  | chrEmpty c =>
    exact ⟨1, by simp [mpegRun]⟩
  | rangeOk lo hi d rest hr =>
    exact ⟨1, by simp [mpegRun, hr]⟩
  | rangeFail lo hi d rest hr =>
    exact ⟨1, by simp [mpegRun, hr]⟩
  | rangeEmpty lo hi =>
    exact ⟨1, by simp [mpegRun]⟩
  | litOk s input rest hs =>
    exact ⟨1, by simp [mpegRun, hs]⟩
  | litFail s input hs =>
    exact ⟨1, by simp [mpegRun, hs]⟩
  | dbg e input =>
    exact ⟨1, by simp [mpegRun]⟩
  | paramFail k input =>
    exact ⟨1, by simp [mpegRun]⟩
  | callOk i args r input rest t hr ha hd ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    have hbeq : (r.arity == args.length) = true := by simpa using ha
    simp only [if_pos hbeq, hf]
  | callFail i args r input hr ha hd ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    have hbeq : (r.arity == args.length) = true := by simpa using ha
    simp only [if_pos hbeq, hf]
  | callMissing i args input hr =>
    exact ⟨1, by simp [mpegRun, hr]⟩
  | callArity i args r input hr ha =>
    exact ⟨1, by simp [mpegRun, hr, ha]⟩
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := mpegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := mpegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | seqFail₁ e₁ e₂ input h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hf]
  | seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := mpegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := mpegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | altL e₁ e₂ input rest t h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hf]
  | altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := mpegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := mpegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := mpegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := mpegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | starNil e input h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hf]
  | starCons e input rest rest' t ts h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := mpegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := mpegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | notOk e input rest t h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hf]
  | notFail e input h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    simp only [hf]

end Shallot.MacroPeg
