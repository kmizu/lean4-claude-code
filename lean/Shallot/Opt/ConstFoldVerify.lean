import Shallot.Opt.ConstFold
import Shallot.Lang.EvalLemmas

/-!
# O1/O2 — constant folding preserves typing and semantics

* O1 (`optExpr_hasType` / `optArgs_hasTypeArgs`): folding a well-typed
  expression yields a well-typed expression of the SAME type. The fold
  helpers produce literals whose types match `binOpSig`/`unOpSig` results
  by computation; the catch-all arms are just the original operator rules.
* O2 (`optExpr_eval` / `optArgs_evalArgs`): at the SAME fuel, every defined
  interpreter outcome is preserved. Division/modulo folding is guarded on
  a nonzero divisor literal, so a folded expression never turns a
  `divByZero` outcome into a value (or vice versa). The known-condition
  `if` cases drop one interpreter step and therefore need fuel
  monotonicity (L4, `eval_mono`) to lift the branch IH from `f` to `f+1`.
-/

namespace Shallot

/-! ## O1 — type preservation -/

theorem foldUnOp_hasType {S : Sig} {Γ : TyCtx} {op : UnOp} {e : Expr}
    (h : HasType S Γ e (unOpSig op).1) :
    HasType S Γ (foldUnOp op e) (unOpSig op).2 := by
  rw [foldUnOp.eq_def]
  split
  · exact .intLit Γ _
  · exact .boolLit Γ _
  · exact .unop Γ op e h

theorem foldBinOp_hasType {S : Sig} {Γ : TyCtx} {op : BinOp} {l r : Expr}
    (hl : HasType S Γ l (binOpSig op).1) (hr : HasType S Γ r (binOpSig op).2.1) :
    HasType S Γ (foldBinOp op l r) (binOpSig op).2.2 := by
  rw [foldBinOp.eq_def]
  split
  -- catch-all arm: the original binop rule
  all_goals try exact .binop Γ _ _ _ hl hr
  -- unguarded literal arms: the folded literal computes to the result type
  all_goals try exact .intLit Γ _
  all_goals try exact .boolLit Γ _
  -- div / mod arms: fold guarded on the divisor literal
  all_goals (
    split
    · exact .binop Γ _ _ _ hl hr
    · exact .intLit Γ _)

mutual

/-- O1: constant folding preserves the typing judgment. -/
theorem optExpr_hasType {S : Sig} {Γ : TyCtx} {e : Expr} {τ : Ty}
    (h : HasType S Γ e τ) : HasType S Γ (optExpr e) τ :=
  match e, τ, h with
  | .intLit n, _, .intLit _ _ => by
    simp only [optExpr]; exact .intLit Γ n
  | .boolLit b, _, .boolLit _ _ => by
    simp only [optExpr]; exact .boolLit Γ b
  | .var x, τ, .var _ _ _ hx => by
    simp only [optExpr]; exact .var Γ x τ hx
  | .unop op e1, _, .unop _ _ _ he => by
    simp only [optExpr]
    exact foldUnOp_hasType (optExpr_hasType he)
  | .binop op l r, _, .binop _ _ _ _ hl hr => by
    simp only [optExpr]
    exact foldBinOp_hasType (optExpr_hasType hl) (optExpr_hasType hr)
  | .ite c t e1, τ, .ite _ _ _ _ _ hc ht he => by
    simp only [optExpr]
    have hc' := optExpr_hasType hc
    have ht' := optExpr_hasType ht
    have he' := optExpr_hasType he
    split
    · exact ht'
    · exact he'
    · exact .ite Γ _ _ _ τ hc' ht' he'
  | .letE x bound body, τ, .letE _ _ _ _ τ₁ _ h₁ h₂ => by
    simp only [optExpr]
    exact .letE Γ x _ _ τ₁ τ (optExpr_hasType h₁) (optExpr_hasType h₂)
  | .call fn args, τ, .call _ _ _ tys _ hf hargs => by
    simp only [optExpr]
    exact .call Γ fn _ tys τ hf (optArgs_hasTypeArgs hargs)

/-- O1, argument-list companion. -/
theorem optArgs_hasTypeArgs {S : Sig} {Γ : TyCtx} {as : Args} {tys : List Ty}
    (h : HasTypeArgs S Γ as tys) : HasTypeArgs S Γ (optArgs as) tys :=
  match as, tys, h with
  | .nil, _, .nil _ => by
    simp only [optArgs]; exact .nil Γ
  | .cons e1 rest, _, .cons _ _ _ τ tys h1 hrest => by
    simp only [optArgs]
    exact .cons Γ _ _ τ tys (optExpr_hasType h1) (optArgs_hasTypeArgs hrest)

end

/-! ## O2 — semantic preservation at the same fuel -/

/-- Inversion: a boolean literal can only evaluate to itself. -/
theorem eval_boolLit_inv {ft : RBNode FunDef} {f : Nat} {env : Env} {b : Bool}
    {res : Except RtErr Value} (h : eval ft f env (.boolLit b) = some res) :
    res = .ok (.vbool b) := by
  cases f with
  | zero => simp [eval] at h
  | succ f =>
    rw [eval.eq_def] at h
    exact (Option.some.inj h).symm

/-- `foldUnOp` never changes a defined outcome at the same fuel: the literal
arm computes on both sides, the catch-all arm IS the original expression. -/
theorem foldUnOp_eval {ft : RBNode FunDef} {f : Nat} {env : Env} {op : UnOp}
    {e : Expr} {res : Except RtErr Value}
    (h : eval ft f env (.unop op e) = some res) :
    eval ft f env (foldUnOp op e) = some res := by
  cases f with
  | zero => simp [eval] at h
  | succ f =>
    cases f with
    | zero =>
      -- fuel 1: the operand evaluates at fuel 0, so `h` is impossible
      simp [eval] at h
    | succ f =>
      rw [foldUnOp.eq_def]
      split
      all_goals try exact h
      all_goals (simp only [eval, evalUnOp] at h ⊢; exact h)

/-- `foldBinOp` never changes a defined outcome at the same fuel. The div/mod
arms only fold when the divisor literal is nonzero — a zero divisor leaves
the expression alone, so both sides still produce `divByZero`. -/
theorem foldBinOp_eval {ft : RBNode FunDef} {f : Nat} {env : Env} {op : BinOp}
    {l r : Expr} {res : Except RtErr Value}
    (h : eval ft f env (.binop op l r) = some res) :
    eval ft f env (foldBinOp op l r) = some res := by
  cases f with
  | zero => simp [eval] at h
  | succ f =>
    cases f with
    | zero =>
      -- fuel 1: the left operand evaluates at fuel 0, so `h` is impossible
      simp [eval] at h
    | succ f =>
      rw [foldBinOp.eq_def]
      split
      -- catch-all arm(s): the fold left the expression alone
      all_goals try exact h
      -- unguarded literal arms: both sides compute
      all_goals try (simp only [eval, evalBinOp] at h ⊢; exact h)
      -- div / mod: the fold fires only for a nonzero divisor literal
      all_goals (
        split
        · exact h
        · rename_i hb
          simp only [eval, evalBinOp] at h ⊢
          rw [if_neg hb] at h
          exact h)

/-- Combined O2 for the mutual `eval`/`evalArgs` pair, by induction on fuel.
Same one-layer-unfolding discipline as `eval_evalArgs_mono` (L4). -/
theorem optExpr_optArgs_eval (ft : RBNode FunDef) (f : Nat) :
    (∀ (env : Env) (e : Expr) (res : Except RtErr Value),
        eval ft f env e = some res → eval ft f env (optExpr e) = some res) ∧
    (∀ (env : Env) (as : Args) (res : Except RtErr (List Value)),
        evalArgs ft f env as = some res → evalArgs ft f env (optArgs as) = some res) := by
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
      | intLit n => simpa only [optExpr] using h
      | boolLit b => simpa only [optExpr] using h
      | var x => simpa only [optExpr] using h
      | unop op e1 =>
        simp only [optExpr]
        apply foldUnOp_eval
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hx : eval ft f env e1 with
        | none => rw [hx] at h; simp at h
        | some v =>
          rw [hx] at h
          rw [ihe env e1 v hx]
          exact h
      | binop op l r =>
        simp only [optExpr]
        apply foldBinOp_eval
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
        simp only [optExpr]
        rw [eval.eq_def] at h
        dsimp only at h
        cases hc : eval ft f env c with
        | none => rw [hc] at h; simp at h
        | some vc =>
          rw [hc] at h
          have hc' : eval ft f env (optExpr c) = some vc := ihe env c vc hc
          split
          · -- condition folded to `true`: one interpreter step is dropped,
            -- lift the branch IH with fuel monotonicity (L4)
            rename_i heq
            rw [heq] at hc'
            cases eval_boolLit_inv hc'
            simp at h
            exact eval_mono (ihe env t res h)
          · -- condition folded to `false`
            rename_i heq
            rw [heq] at hc'
            cases eval_boolLit_inv hc'
            simp at h
            exact eval_mono (ihe env e1 res h)
          · -- condition not a literal: same shape, same fuel
            rw [eval.eq_def]
            dsimp only
            rw [hc']
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
        simp only [optExpr]
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
        simp only [optExpr]
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        -- `cases hf :` substitutes the scrutinee in the goal too
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
            exact h
    · intro env as res h
      cases as with
      | nil => simpa only [optArgs] using h
      | cons e1 rest =>
        simp only [optArgs]
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

/-- O2: constant folding preserves every defined outcome at the SAME fuel. -/
theorem optExpr_eval {ft : RBNode FunDef} {f : Nat} {env : Env} {e : Expr}
    {r : Except RtErr Value} (h : eval ft f env e = some r) :
    eval ft f env (optExpr e) = some r :=
  (optExpr_optArgs_eval ft f).1 env e r h

/-- O2, argument-list companion. -/
theorem optArgs_evalArgs {ft : RBNode FunDef} {f : Nat} {env : Env} {as : Args}
    {r : Except RtErr (List Value)} (h : evalArgs ft f env as = some r) :
    evalArgs ft f env (optArgs as) = some r :=
  (optExpr_optArgs_eval ft f).2 env as r h

end Shallot
