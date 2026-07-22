import MacroPeg.Semantics
import MacroPeg.Fuel

/-!
# T3 — completeness relative to derivation existence (Macro PEG)

The `MacroPeg` analogue of `Shallot.pegRun_complete`: if `MDerives g s e x o`,
then some fuel makes `mpegRun g s f e x = some o`.

## Proof style

Induction on the derivation via the mutual recursor `MDerives.rec` with a real
second motive (`motive_2` below): completeness of the `.callByValuePar` call
cases needs, from `DerivesArgsPar g s input args vals`, a fuel witness for
`evalArgsPar` producing that same `vals`. Leaf rules take fuel `1`; recursive
rules lift sub-witnesses to their `max` (`mpegRun_mono_le`,
`evalArgsPar_mono_le`) and add one for the outer layer. Never `simp only
[mpegRun]`/`[evalArgsPar]` on successor fuel — `rw [X.eq_def]` + `dsimp only`
unfolds exactly one layer.

## `callParArgFail` needed a design fix, found here

`MDerives.callParArgFail` originally let the semantics derive `.fail` for a
call as soon as ANY ONE argument failed, anywhere in the list, with no
constraint on the OTHER arguments. That is unsound relative to what the
interpreter can witness: `evalArgsPar` evaluates arguments strictly
left-to-right and diverges (returns `none` at every fuel) the moment an
EARLIER argument fails to terminate, so a derivation citing a failing
argument past a non-terminating one has no fuel witness at all — completeness
was FALSE, machine-checked via a left-recursive-first-argument counterexample
during development. The fix (now in `Semantics.lean`): `callParArgFail`
requires `args = pre ++ badArg :: post` with an explicit
`hpre : DerivesArgsPar g s input pre preVals` — every argument BEFORE
`badArg` must itself be witnessed as succeeding, exactly mirroring
`evalArgsPar`'s left-to-right short-circuit. With that premise this case is
provable via `evalArgsPar_pre_succ_then_argFail` below, composing `hpre`'s
fuel witness (gets `evalArgsPar` through `pre`) with `badArg`'s own fuel
witness (the short-circuiting failure).
-/

namespace Shallot.MacroPeg

/-! ## Reusable fuel-monotonicity for `evalArgsPar`

`mpegRun_mono_le` (`Fuel.lean`) has no `evalArgsPar` analogue there, so we
derive the single-step and `≤` versions here from
`evalArgsPar_mono_of_mpegRun_mono` (the mono-at-a-fixed-level fact) composed
with `mpegRun_mono`. -/

theorem evalArgsPar_mono {g : MGrammar} {s : Strategy} {f : Nat} {input : List Char}
    {args : List MExp} {r : Option (List MExp)}
    (h : evalArgsPar g s f input args = some r) :
    evalArgsPar g s (f + 1) input args = some r := by
  have hM : ∀ {e : MExp} {x : List Char} {o : MOutcome},
      mpegRun g s f e x = some o → mpegRun g s (f + 1) e x = some o :=
    fun hh => mpegRun_mono hh
  exact evalArgsPar_mono_of_mpegRun_mono hM h

theorem evalArgsPar_mono_le {g : MGrammar} {s : Strategy} {f f' : Nat} {input : List Char}
    {args : List MExp} {r : Option (List MExp)}
    (hle : f ≤ f') (h : evalArgsPar g s f input args = some r) :
    evalArgsPar g s f' input args = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalArgsPar_mono ih

/-! ## Prefix helper (local copies of `Soundness.lean`'s facts, kept
file-private to avoid depending on the soundness module and to avoid name
clashes). -/

private theorem lenChars_append_c (p rest : List Char) :
    lenChars (p ++ rest) = lenChars p + lenChars rest := by
  induction p with
  | nil => simp [lenChars]
  | cons c cs ih => simp only [List.cons_append, lenChars, ih]; omega

private theorem prefixBeforeSuffix_correct_c (p rest : List Char) :
    prefixBeforeSuffix (p ++ rest) rest = p := by
  induction p with
  | nil =>
    rw [prefixBeforeSuffix.eq_def]
    simp only [List.nil_append, beq_iff_eq]
    split
    · rfl
    · rename_i hcond; exact absurd trivial hcond
  | cons c cs ih =>
    rw [prefixBeforeSuffix.eq_def]
    simp only [List.cons_append, beq_iff_eq]
    split
    · rename_i hcond
      exfalso
      simp only [lenChars, lenChars_append_c] at hcond
      omega
    · rw [ih]

/-- If every element of `pre` is derivable (witnessed by `evalArgsPar`
already reaching a full success on `pre`, at the SAME fuel `f`) and
`badArg` fails at that same `f`, then `evalArgsPar` on `pre ++ badArg ::
post` (any `post`) returns `some none` at `f` too — it walks through `pre`
exactly as the `evalArgsPar_mono`-lifted witness says, then hits `badArg`
and short-circuits, never looking at `post` at all. -/
theorem evalArgsPar_pre_succ_then_argFail {g : MGrammar} {s : Strategy} {f : Nat}
    {input : List Char} {preVals : List MExp}
    (pre : List MExp) (badArg : MExp) (post : List MExp)
    (hpre : evalArgsPar g s f input pre = some (some preVals))
    (hbad : mpegRun g s f badArg input = some .fail) :
    evalArgsPar g s f input (pre ++ badArg :: post) = some none := by
  induction pre generalizing preVals with
  | nil =>
    simp only [List.nil_append, evalArgsPar, hbad]
  | cons a as ih =>
    cases h1 : mpegRun g s f a input with
    | none => simp [evalArgsPar, h1] at hpre
    | some o1 =>
      cases o1 with
      | fail => simp [evalArgsPar, h1] at hpre
      | ok t rest =>
        cases h2 : evalArgsPar g s f input as with
        | none => simp [evalArgsPar, h1, h2] at hpre
        | some o2 =>
          cases o2 with
          | none => simp [evalArgsPar, h1, h2] at hpre
          | some vs =>
            have hind := ih h2
            simp only [List.cons_append, evalArgsPar, h1, hind]

theorem mpegRun_complete {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives g s e x o) : ∃ f, mpegRun g s f e x = some o := by
  induction h using MDerives.rec
    (motive_2 := fun input args vals _ =>
      ∃ f, evalArgsPar g s f input args = some (some vals)) with
  | eps input => exact ⟨1, by simp [mpegRun]⟩
  | anyOk c rest => exact ⟨1, by simp [mpegRun]⟩
  | anyFail => exact ⟨1, by simp [mpegRun]⟩
  | chrOk c d rest hcd => exact ⟨1, by simp [mpegRun, hcd]⟩
  | chrFail c d rest hcd => exact ⟨1, by simp [mpegRun, hcd]⟩
  | chrEmpty c => exact ⟨1, by simp [mpegRun]⟩
  | rangeOk lo hi d rest hr => exact ⟨1, by simp [mpegRun, hr]⟩
  | rangeFail lo hi d rest hr => exact ⟨1, by simp [mpegRun, hr]⟩
  | rangeEmpty lo hi => exact ⟨1, by simp [mpegRun]⟩
  | litOk str input rest hs => exact ⟨1, by simp [mpegRun, hs]⟩
  | litFail str input hs => exact ⟨1, by simp [mpegRun, hs]⟩
  | dbg e input => exact ⟨1, by simp [mpegRun]⟩
  | paramFail k input => exact ⟨1, by simp [mpegRun]⟩
  | callNameOk i args r input rest t hs hr ha hd ih =>
    subst hs
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    have hbeq : (r.arity == args.length) = true := by simpa using ha
    simp only [if_pos hbeq, hf]
  | callNameFail i args r input hs hr ha hd ih =>
    subst hs
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [mpegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    have hbeq : (r.arity == args.length) = true := by simpa using ha
    simp only [if_pos hbeq, hf]
  | callParOk i args r input rest vals t hs hr ha hargs hd ihargs ih =>
    subst hs
    obtain ⟨fA, hfA⟩ := ihargs
    obtain ⟨fB, hfB⟩ := ih
    refine ⟨max fA fB + 1, ?_⟩
    have hlA := evalArgsPar_mono_le (Nat.le_max_left fA fB) hfA
    have hlB := mpegRun_mono_le (Nat.le_max_right fA fB) hfB
    rw [mpegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    have hbeq : (r.arity == args.length) = true := by simpa using ha
    simp only [if_pos hbeq, hlA, hlB]
  | callParFail i args r input vals hs hr ha hargs hd ihargs ih =>
    subst hs
    obtain ⟨fA, hfA⟩ := ihargs
    obtain ⟨fB, hfB⟩ := ih
    refine ⟨max fA fB + 1, ?_⟩
    have hlA := evalArgsPar_mono_le (Nat.le_max_left fA fB) hfA
    have hlB := mpegRun_mono_le (Nat.le_max_right fA fB) hfB
    rw [mpegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    have hbeq : (r.arity == args.length) = true := by simpa using ha
    simp only [if_pos hbeq, hlA, hlB]
  | callParArgFail i pre badArg post r input preVals hs hr ha hpre hfail ihpre ih =>
    subst hs
    obtain ⟨fA, hfA⟩ := ihpre
    obtain ⟨fB, hfB⟩ := ih
    refine ⟨max fA fB + 1, ?_⟩
    have hlA := evalArgsPar_mono_le (Nat.le_max_left fA fB) hfA
    have hlB := mpegRun_mono_le (Nat.le_max_right fA fB) hfB
    have hnone := evalArgsPar_pre_succ_then_argFail pre badArg post hlA hlB
    rw [mpegRun.eq_def]
    dsimp only
    rw [hr]
    dsimp only
    have hbeq : (r.arity == (pre ++ badArg :: post).length) = true := by simpa using ha
    simp only [if_pos hbeq, hnone]
  | callMissing i args input hr => exact ⟨1, by simp [mpegRun, hr]⟩
  | callArity i args r input hr ha => exact ⟨1, by simp [mpegRun, hr, ha]⟩
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
  | nil input => exact ⟨0, by simp [evalArgsPar]⟩
  | cons a as input p rest t vs h1 hp h2 ih1 ih2 =>
    obtain ⟨f1, hf1⟩ := ih1
    obtain ⟨f2, hf2⟩ := ih2
    refine ⟨max f1 f2, ?_⟩
    have hl1 := mpegRun_mono_le (Nat.le_max_left f1 f2) hf1
    have hl2 := evalArgsPar_mono_le (Nat.le_max_right f1 f2) hf2
    have hpre : prefixBeforeSuffix input rest = p := by
      rw [hp]; exact prefixBeforeSuffix_correct_c p rest
    rw [evalArgsPar.eq_def]
    dsimp only
    simp only [hl1, hl2, hpre]

end Shallot.MacroPeg
