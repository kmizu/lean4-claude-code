import MacroPeg.Semantics
import Shallot.Peg.Props

/-!
# P1 (macro-PEG) — the suffix invariant for `MDerives`

The `MDerives` analogue of `Shallot.Peg.Props.derives_suffix`: a successful
macro-PEG derivation consumes a prefix, i.e. `MDerives g s e x (.ok t r)`
implies `∃ p, x = p ++ r`. Retrofitted from M-PEG's `CallByName`-only
version with `s` threaded through.

The `.callByValuePar` cases (`callParOk`/`callParFail`/`callParArgFail`) all
reduce to the SAME argument as `callNameOk`/`callNameFail`/etc. — the
consumption fact comes from the sub-derivation `hd`/`hfail` against the SAME
`input` the `.call` itself was run on, so the `hargs : DerivesArgsPar ...`
premise (which does NOT itself constrain `input`/`rest` the way P1 needs) is
simply unused there.

The `.callByValueSeq` cases (`callSeqOk`/`callSeqFail`/`callSeqArgFail`) are
parallel EXCEPT for `callSeqOk`: there the body is derived from the FINAL
THREADED position `mid` (`DerivesArgsSeq g s input args vals mid`), not from
the original `input`, so the sub-derivation `hd` only yields `mid = p ++ rest`.
To recover `input = _ ++ rest` we also need `input = q ++ mid` — the prefix
that threading the arguments consumed. That fact is carried by `motive_3`
(`fun input _ _ final _ => ∃ q, input = q ++ final`) rather than the trivial
`True` used for `motive_2`; the `DerivesArgsSeq` `cons` case discharges it
directly from its own `hp : input = p ++ rest`, no appeal to the argument
sub-derivations needed. `callSeqFail`/`callSeqArgFail` conclude `.fail` and so,
like their Par counterparts, close vacuously. Because `DerivesArgsPar` and
`DerivesArgsSeq` share constructor names, `induction ... with` cannot name both
`nil`/`cons` pairs, so the proof is written with `case ...` blocks (which
disambiguate colliding tags by goal order: `motive_2`/Par before `motive_3`/Seq).
-/

namespace Shallot.MacroPeg

theorem mderives_suffix {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives g s e x o) :
    ∀ t r, o = .ok t r → ∃ p, x = p ++ r := by
  -- `MDerives` is a THREE-way mutual family (with `DerivesArgsPar` AND now
  -- `DerivesArgsSeq`), so `MDerives.rec` takes `motive_2` (Par) and `motive_3`
  -- (Seq). P1 needs no fact about the Par arguments, so `motive_2` is the
  -- trivial `True`. The Seq case is subtly different: `callSeqOk` derives the
  -- callee body from the FINAL THREADED position `mid` (not the original
  -- `input`), so its sub-derivation `hd` only yields `mid = p ++ rest`; to
  -- recover `input = _ ++ rest` we need that threading the arguments consumed a
  -- prefix, `input = q ++ mid`. That fact is exactly what `DerivesArgsSeq`
  -- witnesses (each `cons` step's `hp : input = p ++ rest`), so `motive_3`
  -- carries `∃ q, input = q ++ final` rather than `True`. Because the two
  -- auxiliary inductives share constructor names (`nil`/`cons`), the
  -- `induction ... with` clause cannot name both pairs; we use `case ...`
  -- blocks instead, which disambiguate colliding tags positionally (the first
  -- `case nil`/`case cons` binds the `DerivesArgsPar` goal, the second the
  -- `DerivesArgsSeq` goal, since `motive_2` goals precede `motive_3` goals).
  induction h using MDerives.rec (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun input _ _ final _ => ∃ q, input = q ++ final)
  case eps input => exact fun t r ho => ⟨[], by cases ho; simp⟩
  case anyOk c rest => exact fun t r ho => ⟨[c], by cases ho; simp⟩
  case anyFail => intro _ _ ho; cases ho
  case chrOk c d rest _ => exact fun t r ho => ⟨[d], by cases ho; simp⟩
  case chrFail _ _ _ _ => intro _ _ ho; cases ho
  case chrEmpty _ => intro _ _ ho; cases ho
  case rangeOk lo hi d rest _ => exact fun t r ho => ⟨[d], by cases ho; simp⟩
  case rangeFail _ _ _ _ _ => intro _ _ ho; cases ho
  case rangeEmpty _ _ => intro _ _ ho; cases ho
  case litOk str input rest hs =>
    intro t r ho
    cases ho
    exact stripPrefix?_suffix str input rest hs
  case litFail _ _ _ => intro _ _ ho; cases ho
  case dbg e input => exact fun t r ho => ⟨[], by cases ho; simp⟩
  case paramFail _ _ => intro _ _ ho; cases ho
  case callNameOk i args r input rest t hs hr ha hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  case callNameFail _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  case callParOk i args r input rest vals t hs hr ha hargs ihargs hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  case callParFail _ _ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  case callParArgFail _ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  case callSeqOk i args r input mid rest vals t hs hr ha hargs hd ihargs ih =>
    intro t' r' ho
    cases ho
    obtain ⟨q, hq⟩ := ihargs
    obtain ⟨p, hp⟩ := ih t rest rfl
    exact ⟨q ++ p, by simp [hq, hp]⟩
  case callSeqFail _ _ _ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  case callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  case callMissing _ _ _ _ => intro _ _ ho; cases ho
  case callArity _ _ _ _ _ _ => intro _ _ ho; cases ho
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro t r ho
    cases ho
    obtain ⟨p₁, hp₁⟩ := ih₁ t₁ rest₁ rfl
    obtain ⟨p₂, hp₂⟩ := ih₂ t₂ rest₂ rfl
    exact ⟨p₁ ++ p₂, by simp [hp₁, hp₂]⟩
  case seqFail₁ _ _ _ _ _ => intro _ _ ho; cases ho
  case seqFail₂ _ _ _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  case altL e₁ e₂ input rest t hd ih =>
    intro t' r' ho
    cases ho
    exact ih t rest rfl
  case altR e₁ e₂ input rest t h₁ h₂ _ ih₂ =>
    intro t' r' ho
    cases ho
    exact ih₂ t rest rfl
  case altFail _ _ _ _ _ _ _ => intro _ _ ho; cases ho
  case starNil e input _ _ => exact fun t r ho => ⟨[], by cases ho; simp⟩
  case starCons e input rest rest' t ts h₁ h₂ ih₁ ih₂ =>
    intro t' r' ho
    cases ho
    obtain ⟨p₁, hp₁⟩ := ih₁ t rest rfl
    obtain ⟨p₂, hp₂⟩ := ih₂ ts rest' rfl
    exact ⟨p₁ ++ p₂, by simp [hp₁, hp₂]⟩
  case notOk _ _ _ _ _ => intro _ _ ho; cases ho
  case notFail e input _ => exact fun t r ho => ⟨[], by cases ho; simp⟩
  -- `DerivesArgsPar` nil/cons (`motive_2` = `True`), then `DerivesArgsSeq`
  -- nil/cons (`motive_3` = `∃ q, input = q ++ final`); the repeated `case`
  -- tags disambiguate the collision by goal order (Par before Seq).
  case nil input => trivial
  case cons a as input p rest t vs h1 hp h2 ih => trivial
  case nil input => exact ⟨[], by simp⟩
  case cons a as input p rest final t vs h1 hp h2 ihh1 =>
    -- 12 nameable binders (11 fields + the `motive_1` IH `ihh1` for
    -- `h1 : MDerives …`); the `motive_3` IH for `h2` stays as the goal's
    -- antecedent `(∃ q, rest = q ++ final) → …`, so `intro` it. `hp` threads
    -- `input = p ++ rest`, `hq` threads `rest = q ++ final`.
    intro ih
    obtain ⟨q, hq⟩ := ih
    exact ⟨p ++ q, by simp [hp, hq]⟩

end Shallot.MacroPeg
