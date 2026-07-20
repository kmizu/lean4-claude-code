import Shallot.Lang.Eval

/-!
# L4 — interpreter fuel monotonicity

`eval ft f env e = some r → eval ft (f+1) env e = some r` (and the
`evalArgs` companion — the two are proved together by one induction on
fuel since `eval`/`evalArgs` are mutual), plus the `≤`-lifting
corollaries, mirroring `pegRun_mono`/`pegRun_mono_le` (Peg/Fuel.lean).

Same proof discipline as there: `rw [eval.eq_def]` unfolds exactly ONE
layer; `simp only [eval]` is never applied to a goal whose inner calls sit
at successor fuel (it would expand recursively and destroy the IH rewrite
targets); `cases hx : <scrutinee>` substitutes only the goal, so scrutinee
rewrites in the hypothesis are done with `rw [hx] at h`.
-/

namespace Shallot

/-- Combined fuel monotonicity for the mutual `eval`/`evalArgs` pair. -/
theorem eval_evalArgs_mono (ft : RBNode FunDef) (f : Nat) :
    (∀ (env : Env) (e : Expr) (res : Except RtErr Value),
        eval ft f env e = some res → eval ft (f + 1) env e = some res) ∧
    (∀ (env : Env) (as : Args) (res : Except RtErr (List Value)),
        evalArgs ft f env as = some res → evalArgs ft (f + 1) env as = some res) := by
  induction f with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro env e res h
      simp [eval] at h
    · intro env as res h
      simp [evalArgs] at h
  | succ f ih =>
    obtain ⟨ihe, iha⟩ := ih
    refine ⟨?_, ?_⟩
    · intro env e res h
      cases e with
      | intLit n =>
        rw [eval.eq_def] at h ⊢
        exact h
      | boolLit b =>
        rw [eval.eq_def] at h ⊢
        exact h
      | var x =>
        rw [eval.eq_def] at h ⊢
        exact h
      | unop op e1 =>
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hx : eval ft f env e1 with
        | none => rw [hx] at h; simp at h
        | some v =>
          rw [hx] at h
          rw [ihe env e1 v hx]
          exact h
      | binop op l r =>
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hl : eval ft f env l with
        | none => rw [hl] at h; simp at h
        | some vl =>
          rw [hl] at h
          rw [ihe env l vl hl]
          cases vl with
          | error er => exact h
          | ok v =>
            dsimp only at h ⊢
            cases hr : eval ft f env r with
            | none => rw [hr] at h; simp at h
            | some vr =>
              rw [hr] at h
              rw [ihe env r vr hr]
              exact h
      | ite c t e1 =>
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hc : eval ft f env c with
        | none => rw [hc] at h; simp at h
        | some vc =>
          rw [hc] at h
          rw [ihe env c vc hc]
          cases vc with
          | error er => exact h
          | ok v =>
            cases v with
            | vint n => exact h
            | vbool b =>
              dsimp only at h ⊢
              cases b with
              | true =>
                simp at h ⊢
                exact ihe env t res h
              | false =>
                simp at h ⊢
                exact ihe env e1 res h
      | letE x bound body =>
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hb : eval ft f env bound with
        | none => rw [hb] at h; simp at h
        | some vb =>
          rw [hb] at h
          rw [ihe env bound vb hb]
          cases vb with
          | error er => exact h
          | ok v =>
            dsimp only at h ⊢
            exact ihe ((x, v) :: env) body res h
      | call fn args =>
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        -- `cases hf :` substitutes the scrutinee in the GOAL as well (it is
        -- the same fuel-independent term there), so only `h` needs `rw`.
        cases hf : RBNode.find? ft fn with
        | none =>
          rw [hf] at h
          exact h
        | some d =>
          rw [hf] at h
          dsimp only at h ⊢
          cases ha : evalArgs ft f env args with
          | none => rw [ha] at h; simp at h
          | some va =>
            rw [ha] at h
            rw [iha env args va ha]
            cases va with
            | error er => exact h
            | ok vs =>
              dsimp only at h ⊢
              cases hb : bindParams d.params vs with
              | none =>
                rw [hb] at h
                exact h
              | some env' =>
                rw [hb] at h
                exact ihe env' d.body res h
    · intro env as res h
      cases as with
      | nil =>
        rw [evalArgs.eq_def] at h ⊢
        exact h
      | cons e1 rest =>
        rw [evalArgs.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hx : eval ft f env e1 with
        | none => rw [hx] at h; simp at h
        | some v =>
          rw [hx] at h
          rw [ihe env e1 v hx]
          cases v with
          | error er => exact h
          | ok vv =>
            dsimp only at h ⊢
            cases hr : evalArgs ft f env rest with
            | none => rw [hr] at h; simp at h
            | some vr =>
              rw [hr] at h
              rw [iha env rest vr hr]
              exact h

/-- L4: one extra unit of fuel preserves any defined interpreter outcome. -/
theorem eval_mono {ft : RBNode FunDef} {f : Nat} {env : Env} {e : Expr}
    {r : Except RtErr Value} (h : eval ft f env e = some r) :
    eval ft (f + 1) env e = some r :=
  (eval_evalArgs_mono ft f).1 env e r h

/-- L4, argument-list companion. -/
theorem evalArgs_mono {ft : RBNode FunDef} {f : Nat} {env : Env} {as : Args}
    {r : Except RtErr (List Value)} (h : evalArgs ft f env as = some r) :
    evalArgs ft (f + 1) env as = some r :=
  (eval_evalArgs_mono ft f).2 env as r h

/-- Fuel monotonicity lifted along `≤` (mirror of `pegRun_mono_le`). -/
theorem eval_mono_le {ft : RBNode FunDef} {f f' : Nat} {env : Env} {e : Expr}
    {r : Except RtErr Value} (hle : f ≤ f') (h : eval ft f env e = some r) :
    eval ft f' env e = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact eval_mono ih

/-- `≤`-lifting for `evalArgs`. -/
theorem evalArgs_mono_le {ft : RBNode FunDef} {f f' : Nat} {env : Env} {as : Args}
    {r : Except RtErr (List Value)} (hle : f ≤ f') (h : evalArgs ft f env as = some r) :
    evalArgs ft f' env as = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalArgs_mono ih

end Shallot
