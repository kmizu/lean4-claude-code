import Shallot.Peg.Semantics
import Shallot.Peg.Fuel

/-!
# T2 — completeness relative to derivation existence

If the formal semantics derives outcome `o` for `e` on `x`, then some fuel
level makes the interpreter return `some o`. Left recursion has no
derivation at all, so no totality claim is made — this is the designed
scoping (see Semantics.lean).

Proof: induction on the derivation. Leaf rules take fuel `1` and compute
(rewriting Bool/Option side conditions where present). Each recursive rule
takes the fuel witnesses of its sub-derivations, lifts them to their `max`
via `pegRun_mono_le` (T0), and adds one for the outer layer.

Proof engineering (see Fuel.lean): never `simp only [pegRun]` on successor
fuel — `rw [pegRun.eq_def]` + `dsimp only` unfolds exactly one layer; then
`simp only` with the (lifted) sub-run equations rewrites the inner calls and
iota-reduces the surrounding matches.
-/

namespace Shallot

theorem pegRun_complete {g : Grammar} {e : PExp} {x : List Char} {o : Outcome}
    (h : Derives g e x o) : ∃ f, pegRun g f e x = some o := by
  induction h with
  | eps input =>
    exact ⟨1, by simp [pegRun]⟩
  | anyOk c rest =>
    exact ⟨1, by simp [pegRun]⟩
  | anyFail =>
    exact ⟨1, by simp [pegRun]⟩
  | chrOk c d rest hcd =>
    exact ⟨1, by simp [pegRun, hcd]⟩
  | chrFail c d rest hcd =>
    exact ⟨1, by simp [pegRun, hcd]⟩
  | chrEmpty c =>
    exact ⟨1, by simp [pegRun]⟩
  | rangeOk lo hi d rest hr =>
    exact ⟨1, by simp [pegRun, hr]⟩
  | rangeFail lo hi d rest hr =>
    exact ⟨1, by simp [pegRun, hr]⟩
  | rangeEmpty lo hi =>
    exact ⟨1, by simp [pegRun]⟩
  | litOk s input rest hs =>
    exact ⟨1, by simp [pegRun, hs]⟩
  | litFail s input hs =>
    exact ⟨1, by simp [pegRun, hs]⟩
  | ntOk i e input rest t hr hd ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [pegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    simp only [hf]
  | ntFail i e input hr hd ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [pegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    simp only [hf]
  | ntMissing i input hr =>
    exact ⟨1, by simp [pegRun, hr]⟩
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := pegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := pegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [pegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | seqFail₁ e₁ e₂ input h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [pegRun.eq_def]
    dsimp only
    simp only [hf]
  | seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := pegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := pegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [pegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | altL e₁ e₂ input rest t h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [pegRun.eq_def]
    dsimp only
    simp only [hf]
  | altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := pegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := pegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [pegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := pegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := pegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [pegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | starNil e input h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [pegRun.eq_def]
    dsimp only
    simp only [hf]
  | starCons e input rest rest' t ts h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁
    obtain ⟨f₂, hf₂⟩ := ih₂
    refine ⟨max f₁ f₂ + 1, ?_⟩
    have hl₁ := pegRun_mono_le (Nat.le_max_left f₁ f₂) hf₁
    have hl₂ := pegRun_mono_le (Nat.le_max_right f₁ f₂) hf₂
    rw [pegRun.eq_def]
    dsimp only
    simp only [hl₁, hl₂]
  | notOk e input rest t h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [pegRun.eq_def]
    dsimp only
    simp only [hf]
  | notFail e input h₁ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [pegRun.eq_def]
    dsimp only
    simp only [hf]

end Shallot
