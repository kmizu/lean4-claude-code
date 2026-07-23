import MacroPeg.Semantics

/-!
# T2 — determinism of the macro-PEG derivation relation (call-by-name + call-by-value-par + call-by-value-seq)

`MDerives g s e x o₁ → MDerives g s e x o₂ → o₁ = o₂`. Since `MOutcome.ok`
carries the parse tree, this gives parse-tree uniqueness for free.

## Why a combined recursor

`MDerives` is now `mutual` with `DerivesArgsPar` AND `DerivesArgsSeq` (see
`MacroPeg/Semantics.lean`), so `induction h₁ generalizing o₂` is rejected ("the
induction tactic does not support ... mutually inductive"). The fix is the
explicit combined recursor `MDerives.rec` with real second and third motives —
exactly the template in `MacroPeg/Props.lean`, but here `motive_2`/`motive_3`
must be non-trivial: determinism of `.call` under `.callByValuePar` needs
determinism of `DerivesArgsPar`, and determinism under `.callByValueSeq` needs
determinism of `DerivesArgsSeq`, each provable only AS PART of the same mutual
induction.

Because `DerivesArgsPar` and `DerivesArgsSeq` share the constructor names
`nil`/`cons`, `induction ... with | nil => ...` cannot name both pairs (Lean
rejects "Duplicate alternative name"), so — like `MacroPeg/Props.lean` — this
proof is written with `case ...` blocks, which disambiguate the colliding tags
by goal order: the `motive_2`/Par `nil`/`cons` goals come first, then the
`motive_3`/Seq `nil`/`cons` goals.

## `motive_2` (DerivesArgsPar)

`motive_2` is a CONJUNCTION carrying the two facts about a successful
`DerivesArgsPar g s input args vals` derivation that the `.callByValuePar`
`.call` cases consume:

1. **value-list uniqueness** — two derivations for the same `g s input args`
   force the same `vals` (needed to line up `callParOk` vs `callParOk`, where
   the body is derived from `MExp.subst vals r.body`);
2. **every element succeeds** — for every `a ∈ args`, every outcome of `a` on
   `input` is `.ok` (needed to refute `callParOk`/`callParFail` against a
   `callParArgFail` that claims some argument failed).

The symmetric refutation (`callParArgFail` as the FIRST derivation, against a
`callParOk` whose `hargs'` has no IH) uses the standalone `derivesArgsPar_mem_ok`
below together with `callParArgFail`'s own motive_1 IH.

## `motive_3` (DerivesArgsSeq)

`DerivesArgsSeq` THREADS the input, so its determinism conjunction is subtly
different from `motive_2`:

1. **value-list AND final-position uniqueness** — two derivations
   `DerivesArgsSeq g s input args _ _` force the SAME `vals` and the SAME
   threaded `mid` (both are needed to line up `callSeqOk` vs `callSeqOk`, where
   the body is derived from `MExp.subst vals r.body` starting at `mid`);
2. **split-success at the threaded position** — for every split
   `args = pre ++ badArg :: post` and every witnessed threading
   `DerivesArgsSeq g s input pre _ mid'` of the prefix, every outcome of `badArg`
   at `mid'` (the position the prefix threads to) is `.ok`. Unlike `motive_2`'s
   membership phrasing, this must pin the POSITION each element is evaluated at:
   under call-by-value-seq the k-th argument runs at the input remaining after
   the first k−1 were threaded, not at the original `input`. This conjunct
   refutes `callSeqOk`/`callSeqFail` against a `callSeqArgFail` claiming some
   argument fails at its threaded position.

The symmetric refutation (`callSeqArgFail` as the FIRST derivation, against a
`callSeqOk`/`callSeqFail` whose `hargs'` has no IH) uses the standalone
`derivesArgsSeq_split_ok` below (a position-threaded analogue of
`derivesArgsPar_mem_ok`: it splits the full-list derivation into a prefix
derivation and `badArg`'s success at the prefix's threaded position) together
with `callSeqArgFail`'s own motive_3 IH `ihpre.1` (prefix-position uniqueness,
to identify that threaded position with the `mid` where `hfail` lives) and
motive_1 IH `ih` (determinism of `badArg` at `mid`).

## Proof style for the shared cases

The strategy-independent constructors (`eps`/`any*`/`chr*`/`range*`/`lit*`/
`seq*`/`alt*`/`star*`/`not*`/`dbg`/`paramFail`/`callMissing`/`callArity`) are a
rule-for-rule transcription of `Shallot.derives_det`. Rule-lookup clashes die on
`ruleAtM g.rules i` (`rw [hr] at hr'; injection hr'`), arity clashes on
`r.arity = args.length` vs `≠` (`absurd`), cross-strategy clashes on the
`hs`/`hs'` `Strategy` equalities (`absurd (hs.symm.trans hs') (by decide)`), and
the genuine `ok`/`fail` interactions on the shared sub-derivation IHs.
-/

namespace Shallot.MacroPeg

/-- Every element that appears in a successful `DerivesArgsPar` derivation
itself has a SUCCESS derivation on the same `input`. Structural (no
determinism needed): each `cons` step literally stores the head's success
`h1`, and the tail is handled by the induction hypothesis. Proved by
induction on the argument list with inversion (`cases`) on the derivation,
so it needs neither the mutual recursor nor `motive_2`. -/
theorem derivesArgsPar_mem_ok {g : MGrammar} {s : Strategy} {input : List Char} :
    ∀ {args vals : List MExp}, DerivesArgsPar g s input args vals →
      ∀ {a : MExp}, a ∈ args → ∃ t r, MDerives g s a input (.ok t r) := by
  intro args
  induction args with
  | nil =>
    intro vals h a ha
    cases ha
  | cons b bs ih =>
    intro vals h a ha
    cases h with
    | cons a' as' input' p rest t vs h1 hp h2 =>
      cases ha with
      | head => exact ⟨t, rest, h1⟩
      | tail _ hmem => exact ih h2 hmem

/-- Position-threaded analogue of `derivesArgsPar_mem_ok` for `DerivesArgsSeq`.
Given a successful sequential threading of the WHOLE list
`pre ++ badArg :: post`, it exposes the prefix's own threading
`DerivesArgsSeq g s input pre preVals mid` and `badArg`'s SUCCESS at that
threaded position `mid`. Structural (no determinism): induction on `pre`, each
`cons` step reads off the stored head success and recurses on the threaded
tail. Used for the `callSeqArgFail`-as-first-derivation refutation, where the
`callSeqOk`/`callSeqFail` `h₂` supplies the full-list threading but carries no
IH of its own. -/
theorem derivesArgsSeq_split_ok {g : MGrammar} {s : Strategy} {badArg : MExp} {post : List MExp} :
    ∀ {pre : List MExp} {input : List Char} {vals : List MExp} {final : List Char},
      DerivesArgsSeq g s input (pre ++ badArg :: post) vals final →
      ∃ preVals mid, DerivesArgsSeq g s input pre preVals mid ∧
        ∃ t r, MDerives g s badArg mid (.ok t r) := by
  intro pre
  induction pre with
  | nil =>
    intro input vals final h
    cases h with
    | cons a' as' inp' p' rest' fin' t' vs' h1' hp' h2' =>
      exact ⟨[], input, DerivesArgsSeq.nil input, t', rest', h1'⟩
  | cons c pre' ih =>
    intro input vals final h
    cases h with
    | cons a' as' inp' p' rest' fin' t' vs' h1' hp' h2' =>
      obtain ⟨preVals', mid, hpd, t0, r0, hbad⟩ := ih h2'
      exact ⟨MExp.lit p' :: preVals', mid,
        DerivesArgsSeq.cons c pre' input p' rest' mid t' preVals' h1' hp' hpd, t0, r0, hbad⟩

theorem mderives_det {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char} {o₁ o₂ : MOutcome}
    (h₁ : MDerives g s e x o₁) (h₂ : MDerives g s e x o₂) : o₁ = o₂ := by
  revert h₂
  induction h₁ using MDerives.rec
    (motive_2 := fun input args vals _ =>
      (∀ vals₂, DerivesArgsPar g s input args vals₂ → vals = vals₂) ∧
      (∀ a, a ∈ args → ∀ o, MDerives g s a input o → ∃ t r, o = MOutcome.ok t r))
    (motive_3 := fun input args vals mid _ =>
      (∀ vals₂ mid₂, DerivesArgsSeq g s input args vals₂ mid₂ → vals = vals₂ ∧ mid = mid₂) ∧
      (∀ pre badArg post preVals mid', args = pre ++ badArg :: post →
        DerivesArgsSeq g s input pre preVals mid' →
        ∀ o, MDerives g s badArg mid' o → ∃ t r, o = MOutcome.ok t r))
    generalizing o₂
  case eps input =>
    intro h₂
    cases h₂
    rfl
  case anyOk c rest =>
    intro h₂
    cases h₂
    rfl
  case anyFail =>
    intro h₂
    cases h₂
    rfl
  case chrOk c d rest hcd =>
    intro h₂
    cases h₂ with
    | chrOk _ _ _ _ => rfl
    | chrFail _ _ _ h' => rw [hcd] at h'; exact Bool.noConfusion h'
  case chrFail c d rest hcd =>
    intro h₂
    cases h₂ with
    | chrOk _ _ _ h' => rw [hcd] at h'; exact Bool.noConfusion h'
    | chrFail _ _ _ _ => rfl
  case chrEmpty c =>
    intro h₂
    cases h₂
    rfl
  case rangeOk lo hi d rest hcond =>
    intro h₂
    cases h₂ with
    | rangeOk _ _ _ _ _ => rfl
    | rangeFail _ _ _ _ h' => rw [hcond] at h'; exact Bool.noConfusion h'
  case rangeFail lo hi d rest hcond =>
    intro h₂
    cases h₂ with
    | rangeOk _ _ _ _ h' => rw [hcond] at h'; exact Bool.noConfusion h'
    | rangeFail _ _ _ _ _ => rfl
  case rangeEmpty lo hi =>
    intro h₂
    cases h₂
    rfl
  case litOk str input rest hs =>
    intro h₂
    cases h₂ with
    | litOk _ _ rest' h' =>
      rw [hs] at h'
      injection h' with hrest
      subst hrest
      rfl
    | litFail _ _ h' =>
      rw [hs] at h'
      injection h'
  case litFail str input hs =>
    intro h₂
    cases h₂ with
    | litOk _ _ rest' h' =>
      rw [hs] at h'
      injection h'
    | litFail _ _ _ => rfl
  case dbg e input =>
    intro h₂
    cases h₂ with
    | dbg _ _ => rfl
  case paramFail k input =>
    intro h₂
    cases h₂ with
    | paramFail _ _ => rfl
  -- M-PEG-4: `.lam`/`.callParam` are trivial (unconditional, exactly like
  -- `.dbg`/`.param`'s `paramFail`); `.invoke` mirrors `.call`'s three-way
  -- `Strategy` split with no rule-lookup indirection (`ar`/`bod` are already
  -- part of the `.invoke` node itself, so there is no `callMissing`
  -- analogue and no `rw [hr] at hr'; injection hr'` dance anywhere below).
  case lam ar bod input =>
    intro h₂
    cases h₂ with
    | lam _ _ _ => rfl
  case callParamFail k args input =>
    intro h₂
    cases h₂ with
    | callParamFail _ _ _ => rfl
  case invokeNameOk ar bod args input rest t hs ha hd ih =>
    intro h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | invokeNameFail _ _ _ _ hs' ha' hd' =>
      have h3 := ih hd'
      injection h3
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParArgFail _ _ _ _ _ _ _ hs' _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqFail _ _ _ _ mid' vals' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqArgFail _ _ _ _ _ _ _ _ hs' _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeArity _ _ _ _ ha' =>
      exact absurd ha ha'
  case invokeNameFail ar bod args input hs ha hd ih =>
    intro h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      have h3 := ih hd'
      injection h3
    | invokeNameFail _ _ _ _ hs' ha' hd' => rfl
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' => rfl
    | invokeParArgFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqFail _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeArity _ _ _ _ _ => rfl
  case invokeParOk ar bod args input rest vals t hs ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeNameFail _ _ _ _ hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' =>
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3
    | invokeParArgFail _ _ pre badArg post _ preVals hs' ha' hpre' hfail' =>
      have hmem2 : badArg ∈ pre ++ badArg :: post := by simp
      obtain ⟨t0, r0, hc⟩ := ihargs.2 badArg hmem2 .fail hfail'
      injection hc
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqFail _ _ _ _ mid' vals' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqArgFail _ _ _ _ _ _ _ _ hs' _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeArity _ _ _ _ ha' =>
      exact absurd ha ha'
  case invokeParFail ar bod args input vals hs ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeNameFail _ _ _ _ hs' ha' hd' => rfl
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' => rfl
    | invokeParArgFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqFail _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeArity _ _ _ _ _ => rfl
  case invokeParArgFail ar bod pre badArg post input preVals hs ha hpre hfail ihpre ih =>
    intro h₂
    generalize hargeq : pre ++ badArg :: post = args at h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeNameFail _ _ _ _ hs' ha' hd' => rfl
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      have hmem0 : badArg ∈ pre ++ badArg :: post := by simp
      rw [hargeq] at hmem0
      obtain ⟨t0, r0, hok⟩ := derivesArgsPar_mem_ok hargs' hmem0
      have h3 := ih hok
      injection h3
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' => rfl
    | invokeParArgFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqFail _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeArity _ _ _ _ _ => rfl
  case invokeSeqOk ar bod args input mid rest vals t hs ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeNameFail _ _ _ _ hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParArgFail _ _ _ _ _ _ _ hs' _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      obtain ⟨hveq, hmeq⟩ := ihargs.1 vals' mid' hargs'
      subst hveq
      subst hmeq
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | invokeSeqFail _ _ _ _ mid' vals' hs' ha' hargs' hd' =>
      obtain ⟨hveq, hmeq⟩ := ihargs.1 vals' mid' hargs'
      subst hveq
      subst hmeq
      have h3 := ih hd'
      injection h3
    | invokeSeqArgFail _ _ pre badArg post _ mid' preVals hs' ha' hpre' hfail' =>
      obtain ⟨t0, r0, hc⟩ := ihargs.2 pre badArg post preVals mid' rfl hpre' MOutcome.fail hfail'
      injection hc
    | invokeArity _ _ _ _ ha' =>
      exact absurd ha ha'
  case invokeSeqFail ar bod args input mid vals hs ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeNameFail _ _ _ _ hs' ha' hd' => rfl
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' => rfl
    | invokeParArgFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      obtain ⟨hveq, hmeq⟩ := ihargs.1 vals' mid' hargs'
      subst hveq
      subst hmeq
      have h3 := ih hd'
      injection h3
    | invokeSeqFail _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeArity _ _ _ _ _ => rfl
  case invokeSeqArgFail ar bod pre badArg post input mid preVals hs ha hpre hfail ihpre ih =>
    intro h₂
    generalize hargeq : pre ++ badArg :: post = args at h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeNameFail _ _ _ _ hs' ha' hd' => rfl
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' => rfl
    | invokeParArgFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqOk _ _ _ _ mid'' rest' vals' t' hs' ha' hargs' hd' =>
      rw [← hargeq] at hargs'
      obtain ⟨preVals', mid', hpd, t0, r0, hbad⟩ := derivesArgsSeq_split_ok hargs'
      obtain ⟨_, hmeq⟩ := ihpre.1 preVals' mid' hpd
      subst hmeq
      have h3 := ih hbad
      injection h3
    | invokeSeqFail _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeArity _ _ _ _ _ => rfl
  case invokeArity ar bod args input ha =>
    intro h₂
    cases h₂ with
    | invokeNameOk _ _ _ _ rest' t' hs' ha' hd' =>
      exact absurd ha' ha
    | invokeNameFail _ _ _ _ hs' ha' hd' => rfl
    | invokeParOk _ _ _ _ rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd ha' ha
    | invokeParFail _ _ _ _ vals' hs' ha' hargs' hd' => rfl
    | invokeParArgFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqOk _ _ _ _ mid' rest' vals' t' hs' ha' hargs' hd' =>
      exact absurd ha' ha
    | invokeSeqFail _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | invokeArity _ _ _ _ _ => rfl
  case callNameOk i args r input rest t hs hr ha hd ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | callNameFail _ _ r' _ hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParArgFail _ _ _ _ _ _ _ hs' _ _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqFail _ _ r' _ mid' vals' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqArgFail _ _ _ _ _ _ _ _ hs' _ _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callMissing _ _ _ hr' =>
      rw [hr] at hr'
      injection hr'
    | callArity _ _ r' _ hr' ha' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha ha'
  case callNameFail i args r input hs hr ha hd ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have h3 := ih hd'
      injection h3
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  case callParOk i args r input rest vals t hs hr ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3
    | callParArgFail _ pre badArg post r' _ preVals hs' hr' ha' hpre' hfail' =>
      have hmem2 : badArg ∈ pre ++ badArg :: post := by simp
      obtain ⟨t0, r0, hc⟩ := ihargs.2 badArg hmem2 .fail hfail'
      injection hc
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqFail _ _ r' _ mid' vals' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqArgFail _ _ _ _ _ _ _ _ hs' _ _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callMissing _ _ _ hr' =>
      rw [hr] at hr'
      injection hr'
    | callArity _ _ r' _ hr' ha' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha ha'
  case callParFail i args r input vals hs hr ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      have hveq := ihargs.1 vals' hargs'
      subst hveq
      have h3 := ih hd'
      injection h3
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  case callParArgFail i pre badArg post r input preVals hs hr ha hpre hfail ihpre ih =>
    intro h₂
    -- `.call`'s argument list is the structured `pre ++ badArg :: post`, on
    -- which `cases h₂` cannot solve the append-index equation for the
    -- `callParArgFail`-vs-`callParArgFail` sub-goal; generalize it to a plain
    -- variable first so dependent elimination succeeds for every constructor.
    generalize hargeq : pre ++ badArg :: post = args at h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      have hmem0 : badArg ∈ pre ++ badArg :: post := by simp
      rw [hargeq] at hmem0
      obtain ⟨t0, r0, hok⟩ := derivesArgsPar_mem_ok hargs' hmem0
      have h3 := ih hok
      injection h3
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  case callSeqOk i args r input mid rest vals t hs hr ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParArgFail _ _ _ _ _ _ _ hs' _ _ _ _ =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      obtain ⟨hveq, hmeq⟩ := ihargs.1 vals' mid' hargs'
      subst hveq
      subst hmeq
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | callSeqFail _ _ r' _ mid' vals' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      obtain ⟨hveq, hmeq⟩ := ihargs.1 vals' mid' hargs'
      subst hveq
      subst hmeq
      have h3 := ih hd'
      injection h3
    | callSeqArgFail _ pre badArg post r' _ mid' preVals hs' hr' ha' hpre' hfail' =>
      obtain ⟨t0, r0, hc⟩ := ihargs.2 pre badArg post preVals mid' rfl hpre' MOutcome.fail hfail'
      injection hc
    | callMissing _ _ _ hr' =>
      rw [hr] at hr'
      injection hr'
    | callArity _ _ r' _ hr' ha' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha ha'
  case callSeqFail i args r input mid vals hs hr ha hargs hd ihargs ih =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      obtain ⟨hveq, hmeq⟩ := ihargs.1 vals' mid' hargs'
      subst hveq
      subst hmeq
      have h3 := ih hd'
      injection h3
    | callSeqFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  case callSeqArgFail i pre badArg post r input mid preVals hs hr ha hpre hfail ihpre ih =>
    intro h₂
    -- Same append-index obstruction as `callParArgFail`: generalize the
    -- structured argument list to a variable before dependent elimination.
    generalize hargeq : pre ++ badArg :: post = args at h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      exact absurd (hs.symm.trans hs') (by decide)
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqOk _ _ r' _ mid'' rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [← hargeq] at hargs'
      obtain ⟨preVals', mid', hpd, t0, r0, hbad⟩ := derivesArgsSeq_split_ok hargs'
      obtain ⟨_, hmeq⟩ := ihpre.1 preVals' mid' hpd
      subst hmeq
      have h3 := ih hbad
      injection h3
    | callSeqFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  case callMissing i args input hr =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr'
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr'
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr'
    | callSeqFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  case callArity i args r input hr ha =>
    intro h₂
    cases h₂ with
    | callNameOk _ _ r' _ rest' t' hs' hr' ha' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha' ha
    | callNameFail _ _ r' _ hs' hr' ha' hd' => rfl
    | callParOk _ _ r' _ rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha' ha
    | callParFail _ _ r' _ vals' hs' hr' ha' hargs' hd' => rfl
    | callParArgFail _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqOk _ _ r' _ mid' rest' vals' t' hs' hr' ha' hargs' hd' =>
      rw [hr] at hr'
      injection hr' with he
      subst he
      exact absurd ha' ha
    | callSeqFail _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callSeqArgFail _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    | callMissing _ _ _ hr' => rfl
    | callArity _ _ r' _ hr' ha' => rfl
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ hd₁ hd₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | seqOk _ _ _ rest₁' rest₂' t₁' t₂' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4 with ht' hrest'
      subst ht'
      subst hrest'
      rfl
    | seqFail₁ _ _ _ hd₁' =>
      have h3 := ih₁ hd₁'
      injection h3
    | seqFail₂ _ _ _ rest₁' t₁' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4
  case seqFail₁ e₁ e₂ input hd₁ ih₁ =>
    intro h₂
    cases h₂ with
    | seqOk _ _ _ rest₁' rest₂' t₁' t₂' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3
    | seqFail₁ _ _ _ _ => rfl
    | seqFail₂ _ _ _ rest₁' t₁' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3
  case seqFail₂ e₁ e₂ input rest₁ t₁ hd₁ hd₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | seqOk _ _ _ rest₁' rest₂' t₁' t₂' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4
    | seqFail₁ _ _ _ hd₁' =>
      have h3 := ih₁ hd₁'
      injection h3
    | seqFail₂ _ _ _ rest₁' t₁' hd₁' hd₂' => rfl
  case altL e₁ e₂ input rest t hd ih =>
    intro h₂
    cases h₂ with
    | altL _ _ _ rest' t' hd' =>
      have h3 := ih hd'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | altR _ _ _ rest' t' hf' hok' =>
      have h3 := ih hf'
      injection h3
    | altFail _ _ _ hf₁' hf₂' =>
      have h3 := ih hf₁'
      injection h3
  case altR e₁ e₂ input rest t hf hok ihf ihok =>
    intro h₂
    cases h₂ with
    | altL _ _ _ rest' t' hd' =>
      have h3 := ihf hd'
      injection h3
    | altR _ _ _ rest' t' hf' hok' =>
      have h3 := ihok hok'
      injection h3 with ht hrest
      subst ht
      subst hrest
      rfl
    | altFail _ _ _ hf₁' hf₂' =>
      have h3 := ihok hf₂'
      injection h3
  case altFail e₁ e₂ input hf₁ hf₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | altL _ _ _ rest' t' hd' =>
      have h3 := ih₁ hd'
      injection h3
    | altR _ _ _ rest' t' hf' hok' =>
      have h3 := ih₂ hok'
      injection h3
    | altFail _ _ _ _ _ => rfl
  case starNil e input hf ih =>
    intro h₂
    cases h₂ with
    | starNil _ _ _ => rfl
    | starCons _ _ rest₁' rest₂' t' ts' hd₁' hd₂' =>
      have h3 := ih hd₁'
      injection h3
  case starCons e input rest rest' t ts hd₁ hd₂ ih₁ ih₂ =>
    intro h₂
    cases h₂ with
    | starNil _ _ hf' =>
      have h3 := ih₁ hf'
      injection h3
    | starCons _ _ rest₁' rest₂' t' ts' hd₁' hd₂' =>
      have h3 := ih₁ hd₁'
      injection h3 with ht hrest
      subst ht
      subst hrest
      have h4 := ih₂ hd₂'
      injection h4 with hts hrest'
      subst hts
      subst hrest'
      rfl
  case notOk e input rest t hd ih =>
    intro h₂
    cases h₂ with
    | notOk _ _ rest' t' hd' => rfl
    | notFail _ _ hf' =>
      have h3 := ih hf'
      injection h3
  case notFail e input hf ih =>
    intro h₂
    cases h₂ with
    | notOk _ _ rest' t' hd' =>
      have h3 := ih hd'
      injection h3
    | notFail _ _ _ => rfl
  -- `DerivesArgsPar` nil/cons (`motive_2`) first, then `DerivesArgsSeq` nil/cons
  -- (`motive_3`); the repeated `case` tags disambiguate by goal order.
  case nil input =>
    refine ⟨?_, ?_⟩
    · intro vals₂ h
      cases h
      rfl
    · intro a ha
      cases ha
  case cons a as input p rest t vs h1 hp h2 ih1 ih2 =>
    refine ⟨?_, ?_⟩
    · intro vals₂ h
      cases h with
      | cons a' as' input' p' rest' t' vs' h1' hp' h2' =>
        have h3 := ih1 h1'
        injection h3 with _ hrest
        subst hrest
        have hpp : p ++ rest = p' ++ rest := by rw [← hp, ← hp']
        have hpeq := List.append_cancel_right hpp
        have hvv := ih2.1 vs' h2'
        rw [hpeq, hvv]
    · intro a0 ha0
      cases ha0 with
      | head => intro o hd0; exact ⟨t, rest, (ih1 hd0).symm⟩
      | tail _ hmem => exact ih2.2 a0 hmem
  case nil input =>
    refine ⟨?_, ?_⟩
    · intro vals₂ mid₂ h
      cases h with
      | nil => exact ⟨rfl, rfl⟩
    · intro pre badArg' post preVals mid' heq hpre o hd
      cases pre <;> simp at heq
  case cons a as input p rest final t vs h1 hp h2 ih1 =>
    intro ih2
    refine ⟨?_, ?_⟩
    · intro vals₂ mid₂ h
      cases h with
      | cons a' as' input' p' rest' final' t' vs' h1' hp' h2' =>
        have h3 := ih1 h1'
        injection h3 with _ hrest
        subst hrest
        obtain ⟨hvv, hmm⟩ := ih2.1 _ _ h2'
        have hpp : p ++ rest = p' ++ rest := by rw [← hp, ← hp']
        have hpeq := List.append_cancel_right hpp
        subst hpeq
        subst hvv
        exact ⟨rfl, hmm⟩
    · intro pre badArg' post preVals mid' heq hpre o hd
      cases pre with
      | nil =>
        injection heq with hba has
        cases hpre with
        | nil =>
          subst hba
          exact ⟨t, rest, (ih1 hd).symm⟩
      | cons c pre' =>
        injection heq with hac has
        cases hpre with
        | cons ca cas cinp cp crest cfin ct cvs ch1 chp ch2 =>
          subst hac
          have h3 := ih1 ch1
          injection h3 with _ hcr
          subst hcr
          exact ih2.2 pre' badArg' post cvs mid' has ch2 o hd

end Shallot.MacroPeg
