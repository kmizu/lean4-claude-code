import MacroPeg.Semantics
import MacroPeg.Interp
import MacroPeg.Props

/-!
# T1 — interpreter soundness (Macro PEG, call-by-name + call-by-value-par + call-by-value-seq)

`mpegRun g s f e x = some o → MDerives g s e x o`. Mirrors
`Shallot.Peg.Soundness.pegRun_sound`/M-PEG's own prior `mpegRun_sound` for
the shared cases, retrofitted with `s` threaded through and new
`.callByValuePar` / `.callByValueSeq` branches.

Just like `mpegRun_mono`/`evalArgsPar_mono_of_mpegRun_mono` in `Fuel.lean`,
the `.callByValuePar` case does NOT need a genuinely mutual induction: a
companion fact `evalArgsPar_sound_of_mpegRun_sound` — "if `mpegRun`-sound
holds at fuel level `f`, then whatever `evalArgsPar` returns at that same
level `f` is derivable via `DerivesArgsPar`" — is provable by plain list
induction on the argument list, taking mpegRun-sound-at-`f` as a parameter.
That parameter is exactly `ih` inside `mpegRun_sound`'s own
`induction f generalizing e x o with | succ f ih => ...`, since unfolding
`mpegRun` at `f+1` uses `evalArgsPar` at the INNER fuel `f`, and `ih` is
soundness at that same `f`.

The `.callByValueSeq` case is structurally identical, with its own companion
`evalArgsSeq_sound_of_mpegRun_sound`. Two twists mirror `Fuel.lean`'s Seq
work: (a) `evalArgsSeq`'s `cons` threads the remainder `rest` into the tail's
evaluation (unlike `evalArgsPar`, which keeps `input` fixed), so the list
induction GENERALIZES over `input` — otherwise `ih` would be pinned to the
original `input` and useless at `rest`; and (b) the success conclusion must
produce BOTH a `DerivesArgsSeq` derivation AND the threaded final position
`mid`, and the failure conclusion pins the failing argument to that threaded
`mid` (not to `input`), so its existential carries an extra `mid` witness.
The callee body is then derived from `mid` (`callSeqOk`/`callSeqFail`), not
from the original `x`.

Proof-engineering notes (same discipline as `Fuel.lean`): `rw
[mpegRun.eq_def]`/`rw [evalArgsPar.eq_def]`/`rw [evalArgsSeq.eq_def]` +
`dsimp only` to unfold one layer; `by_cases hbeq : (r.arity == args.length)
= true` + `simp only [if_pos/if_neg]` for the arity check (Bool, not Prop `≠`
— matches `Fuel.lean`'s working idiom); the interpreter's inner-star
`some .fail` branch is refuted by `mStarNeverFails`.
-/

namespace Shallot.MacroPeg

/-- A star never fails: the only `MDerives` rules concluding at a `.star`
expression are `starNil` and `starCons`, and both produce `.ok`. -/
theorem mStarNeverFails {g : MGrammar} {s : Strategy} {e : MExp} {input : List Char} {o : MOutcome}
    (h : MDerives g s (.star e) input o) : o ≠ .fail := by
  intro hf
  subst hf
  cases h

/-- Local Bool inversion helper: `¬(b = true)` gives `b = false`. -/
theorem eq_false_of_not_eq_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

theorem lenChars_append (p rest : List Char) :
    lenChars (p ++ rest) = lenChars p + lenChars rest := by
  induction p with
  | nil => simp [lenChars]
  | cons c cs ih => simp only [List.cons_append, lenChars, ih]; omega

/-- `prefixBeforeSuffix` computes exactly the prefix it's supposed to:
given ANY split `p ++ rest`, stripping `rest` back off returns `p`. Needed
to identify `evalArgsPar`'s computed `.lit (prefixBeforeSuffix input rest)`
with the `.lit p` that `DerivesArgsPar.cons` expects, where `p` comes from
`mderives_suffix`-style reasoning (`hd1`'s own P1 fact) rather than from
`prefixBeforeSuffix` itself. -/
theorem prefixBeforeSuffix_correct (p rest : List Char) :
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
      simp only [lenChars, lenChars_append] at hcond
      omega
    · rw [ih]

/-- If `mpegRun` is sound at fuel level `f` (the exact fact
`mpegRun_sound`'s own induction hands you as `ih`), then whatever
`evalArgsPar` returns at that same level is derivable via `DerivesArgsPar`
(success case) or witnesses a failing argument (failure case). Plain
structural induction on the argument list. -/
theorem evalArgsPar_sound_of_mpegRun_sound {g : MGrammar} {s : Strategy} {f : Nat}
    (hM : ∀ {e : MExp} {x : List Char} {o : MOutcome},
      mpegRun g s f e x = some o → MDerives g s e x o) :
    ∀ {input : List Char} {args : List MExp} {r : Option (List MExp)},
      evalArgsPar g s f input args = some r →
        (∀ vals, r = some vals → DerivesArgsPar g s input args vals) ∧
        (r = none → ∃ pre badArg post preVals, args = pre ++ badArg :: post ∧
          DerivesArgsPar g s input pre preVals ∧ MDerives g s badArg input .fail) := by
  intro input args
  induction args with
  | nil =>
    intro r h
    simp only [evalArgsPar] at h
    cases h
    refine ⟨?_, ?_⟩
    · intro vals hv; cases hv; exact DerivesArgsPar.nil input
    · intro hn; cases hn
  | cons a as ih =>
    intro r h
    rw [evalArgsPar.eq_def] at h
    dsimp only at h
    cases h1 : mpegRun g s f a input with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some o1 =>
      rw [h1] at h
      have hd1 := hM h1
      cases o1 with
      | fail =>
        dsimp only at h
        cases h
        refine ⟨?_, ?_⟩
        · intro vals hv; cases hv
        · intro _
          exact ⟨[], a, as, [], rfl, DerivesArgsPar.nil input, hd1⟩
      | ok t rest =>
        dsimp only at h
        cases h2 : evalArgsPar g s f input as with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some o2 =>
          rw [h2] at h
          obtain ⟨ihSome, ihNone⟩ := ih h2
          cases o2 with
          | none =>
            dsimp only at h
            cases h
            refine ⟨?_, ?_⟩
            · intro vals hv; cases hv
            · intro _
              obtain ⟨pre', badArg, post, preVals', heq, hpre', hbad⟩ := ihNone rfl
              obtain ⟨p, hp⟩ := mderives_suffix hd1 t rest rfl
              refine ⟨a :: pre', badArg, post, .lit p :: preVals', by simp [heq], ?_, hbad⟩
              exact DerivesArgsPar.cons a pre' input p rest t preVals' hd1 hp hpre'
          | some vs =>
            dsimp only at h
            cases h
            refine ⟨?_, ?_⟩
            · intro vals hv
              cases hv
              obtain ⟨p, hp⟩ := mderives_suffix hd1 t rest rfl
              have hpeq : prefixBeforeSuffix input rest = p := by
                rw [hp]; exact prefixBeforeSuffix_correct p rest
              rw [hpeq]
              exact DerivesArgsPar.cons a as input p rest t vs hd1 hp (ihSome vs rfl)
            · intro hcon; exact absurd hcon (by simp)

/-- Seq analogue of `evalArgsPar_sound_of_mpegRun_sound`. If `mpegRun` is
sound at fuel level `f` (the exact fact `mpegRun_sound`'s own induction hands
you as `ih`), then whatever `evalArgsSeq` returns at that same level is
derivable via `DerivesArgsSeq` — the success case producing BOTH the
derivation AND the threaded final position `mid`, the failure case witnessing
a failing argument AT its threaded position `mid` (not at the original
`input`). Because `evalArgsSeq`'s `cons` threads the remainder `rest` into
the tail's evaluation (unlike `evalArgsPar`, which keeps `input` fixed), the
list induction GENERALIZES over `input` — exactly as
`evalArgsSeq_mono_of_mpegRun_mono` does in `Fuel.lean` — so `ih` is available
at the threaded `rest`, not pinned to the original `input`. -/
theorem evalArgsSeq_sound_of_mpegRun_sound {g : MGrammar} {s : Strategy} {f : Nat}
    (hM : ∀ {e : MExp} {x : List Char} {o : MOutcome},
      mpegRun g s f e x = some o → MDerives g s e x o) :
    ∀ {input : List Char} {args : List MExp} {r : Option (List MExp × List Char)},
      evalArgsSeq g s f input args = some r →
        (∀ vals mid, r = some (vals, mid) → DerivesArgsSeq g s input args vals mid) ∧
        (r = none → ∃ pre badArg post preVals mid, args = pre ++ badArg :: post ∧
          DerivesArgsSeq g s input pre preVals mid ∧ MDerives g s badArg mid .fail) := by
  intro input args
  induction args generalizing input with
  | nil =>
    intro r h
    simp only [evalArgsSeq] at h
    cases h
    refine ⟨?_, ?_⟩
    · intro vals mid hv; cases hv; exact DerivesArgsSeq.nil input
    · intro hn; cases hn
  | cons a as ih =>
    intro r h
    rw [evalArgsSeq.eq_def] at h
    dsimp only at h
    cases h1 : mpegRun g s f a input with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some o1 =>
      rw [h1] at h
      have hd1 := hM h1
      cases o1 with
      | fail =>
        dsimp only at h
        cases h
        refine ⟨?_, ?_⟩
        · intro vals mid hv; cases hv
        · intro _
          exact ⟨[], a, as, [], input, rfl, DerivesArgsSeq.nil input, hd1⟩
      | ok t rest =>
        dsimp only at h
        cases h2 : evalArgsSeq g s f rest as with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some o2 =>
          rw [h2] at h
          obtain ⟨ihSome, ihNone⟩ := ih h2
          cases o2 with
          | none =>
            dsimp only at h
            cases h
            refine ⟨?_, ?_⟩
            · intro vals mid hv; cases hv
            · intro _
              obtain ⟨pre', badArg, post, preVals', mid', heq, hpre', hbad⟩ := ihNone rfl
              obtain ⟨p, hp⟩ := mderives_suffix hd1 t rest rfl
              refine ⟨a :: pre', badArg, post, .lit p :: preVals', mid', by simp [heq], ?_, hbad⟩
              exact DerivesArgsSeq.cons a pre' input p rest mid' t preVals' hd1 hp hpre'
          | some p2 =>
            cases p2 with
            | mk vs final =>
              dsimp only at h
              cases h
              refine ⟨?_, ?_⟩
              · intro vals mid hv
                cases hv
                obtain ⟨p, hp⟩ := mderives_suffix hd1 t rest rfl
                have hpeq : prefixBeforeSuffix input rest = p := by
                  rw [hp]; exact prefixBeforeSuffix_correct p rest
                rw [hpeq]
                exact DerivesArgsSeq.cons a as input p rest final t vs hd1 hp (ihSome vs final rfl)
              · intro hcon; exact absurd hcon (by simp)

/-- T1 — soundness: whatever the interpreter returns is derivable. -/
theorem mpegRun_sound {g : MGrammar} {s : Strategy} {f : Nat} {e : MExp} {x : List Char} {o : MOutcome}
    (h : mpegRun g s f e x = some o) : MDerives g s e x o := by
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
    | lit str =>
      dsimp only at h
      cases hs : stripPrefix? str x with
      | some rest =>
        rw [hs] at h
        dsimp only at h
        cases h
        exact MDerives.litOk str x rest hs
      | none =>
        rw [hs] at h
        dsimp only at h
        cases h
        exact MDerives.litFail str x hs
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
          cases s with
          | callByName =>
            dsimp only at h
            cases h1 : mpegRun g .callByName f (MExp.subst args r.body) x with
            | none => rw [h1] at h; exact absurd h (by simp)
            | some o1 =>
              rw [h1] at h
              cases o1 with
              | fail =>
                dsimp only at h
                cases h
                exact MDerives.callNameFail i args r x rfl hr ha (ih h1)
              | ok t rest =>
                dsimp only at h
                cases h
                exact MDerives.callNameOk i args r x rest t rfl hr ha (ih h1)
          | callByValuePar =>
            dsimp only at h
            cases h1 : evalArgsPar g .callByValuePar f x args with
            | none => rw [h1] at h; exact absurd h (by simp)
            | some o1 =>
              rw [h1] at h
              obtain ⟨hSome, hNone⟩ := evalArgsPar_sound_of_mpegRun_sound (@ih) h1
              cases o1 with
              | none =>
                dsimp only at h
                cases h
                obtain ⟨pre, badArg, post, preVals, heq, hpre, hbad⟩ := hNone rfl
                rw [heq]
                exact MDerives.callParArgFail i pre badArg post r x preVals rfl hr (heq ▸ ha) hpre hbad
              | some vals =>
                dsimp only at h
                have hargs := hSome vals rfl
                cases h2 : mpegRun g .callByValuePar f (MExp.subst vals r.body) x with
                | none => rw [h2] at h; exact absurd h (by simp)
                | some o2 =>
                  rw [h2] at h
                  cases o2 with
                  | fail =>
                    dsimp only at h
                    cases h
                    exact MDerives.callParFail i args r x vals rfl hr ha hargs (ih h2)
                  | ok t rest =>
                    dsimp only at h
                    cases h
                    exact MDerives.callParOk i args r x rest vals t rfl hr ha hargs (ih h2)
          | callByValueSeq =>
            dsimp only at h
            cases h1 : evalArgsSeq g .callByValueSeq f x args with
            | none => rw [h1] at h; exact absurd h (by simp)
            | some o1 =>
              rw [h1] at h
              obtain ⟨hSome, hNone⟩ := evalArgsSeq_sound_of_mpegRun_sound (@ih) h1
              cases o1 with
              | none =>
                dsimp only at h
                cases h
                obtain ⟨pre, badArg, post, preVals, mid, heq, hpre, hbad⟩ := hNone rfl
                rw [heq]
                exact MDerives.callSeqArgFail i pre badArg post r x mid preVals rfl hr (heq ▸ ha) hpre hbad
              | some p =>
                cases p with
                | mk vals mid =>
                  dsimp only at h
                  have hargs := hSome vals mid rfl
                  cases h2 : mpegRun g .callByValueSeq f (MExp.subst vals r.body) mid with
                  | none => rw [h2] at h; exact absurd h (by simp)
                  | some o2 =>
                    rw [h2] at h
                    cases o2 with
                    | fail =>
                      dsimp only at h
                      cases h
                      exact MDerives.callSeqFail i args r x mid vals rfl hr ha hargs (ih h2)
                    | ok t rest =>
                      dsimp only at h
                      cases h
                      exact MDerives.callSeqOk i args r x mid rest vals t rfl hr ha hargs (ih h2)
        · simp only [if_neg hbeq] at h
          cases h
          have hne : r.arity ≠ args.length := by
            intro he
            exact hbeq (by simp [he])
          exact MDerives.callArity i args r x hr hne
    | seq e₁ e₂ =>
      dsimp only at h
      cases h1 : mpegRun g s f e₁ x with
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
          cases h2 : mpegRun g s f e₂ rest₁ with
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
      cases h1 : mpegRun g s f e₁ x with
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
          cases h2 : mpegRun g s f e₂ x with
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
      cases h1 : mpegRun g s f e x with
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
          cases h2 : mpegRun g s f (.star e) rest with
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
      cases h1 : mpegRun g s f e x with
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
