import Shallot.Lang.TypeCheckVerify
import Shallot.Lang.EvalLemmas
import Shallot.Data.RBVerify
import Shallot.Opt.ConstFoldVerify

/-!
# L5 — type soundness for the Shallot interpreter (M8), plus O3

* `ValHasTy` / `ValsHasTy` / `EnvTy`: value, value-list and environment
  typing. `EnvTy` is POINTWISE (every typed variable is bound to a value of
  that type) — both `lookupVal` and `lookupTy` are first-match by `beqStr`,
  so consing a binding preserves the correspondence on both sides at once.
* Bridge (spec item 2): `lookupSig` on the signature list agrees with
  `RBNode.find?` on the interpreter's function table, via R6
  (`find_fromList`) plus a list induction — both lookups are first-match
  by the SAME key comparison (`beqStr` is DEFINED as `cmpStr = .eq`).
* **L5** (`eval_sound`): a well-typed expression never gets stuck — every
  defined interpreter outcome is either a `divByZero` error (`okErr`) or a
  value of the static type. One induction on fuel carrying the mutual
  `eval`/`evalArgs` statements; same one-layer-unfolding discipline as L4
  (`rw [eval.eq_def]`, never `simp only [eval]` at successor fuel).
* `runProgram_sound`: the program-level corollary through the verified
  typechecker (L3 `checkProgram_sound`).
* **O3** (`optProgram_run`): whole-program constant folding preserves every
  defined outcome — `find?_mkFunTable_opt` (the optimized table is the
  `optFun`-image of the original, again via R6 + list induction; `optFun`
  preserves `name`), then a table-aware re-run of the O2 induction whose
  call case steps into the callee's optimized body.
-/

namespace Shallot

/-! ## Value and environment typing -/

/-- Value typing: `vint` inhabits `int`, `vbool` inhabits `bool`. -/
inductive ValHasTy : Value → Ty → Prop where
  | vint (n : Int) : ValHasTy (.vint n) .int
  | vbool (b : Bool) : ValHasTy (.vbool b) .bool

/-- Pointwise value-list typing (for argument lists). -/
inductive ValsHasTy : List Value → List Ty → Prop where
  | nil : ValsHasTy [] []
  | cons {v : Value} {τ : Ty} {vs : List Value} {tys : List Ty} :
      ValHasTy v τ → ValsHasTy vs tys → ValsHasTy (v :: vs) (τ :: tys)

/-- Environment typing, pointwise: every variable the context types is
bound in the environment to a value of that type. -/
def EnvTy (env : Env) (Γ : TyCtx) : Prop :=
  ∀ (x : String) (τ : Ty), lookupTy Γ x = some τ →
    ∃ v, lookupVal env x = some v ∧ ValHasTy v τ

/-- The ONLY runtime error a well-typed program can produce. -/
def okErr (er : RtErr) : Prop := er = RtErr.divByZero

theorem ValHasTy.int_inv {v : Value} (h : ValHasTy v Ty.int) :
    ∃ n, v = Value.vint n := by
  cases h with
  | vint n => exact ⟨n, rfl⟩

theorem ValHasTy.bool_inv {v : Value} (h : ValHasTy v Ty.bool) :
    ∃ b, v = Value.vbool b := by
  cases h with
  | vbool b => exact ⟨b, rfl⟩

theorem EnvTy_nil : EnvTy [] [] := by
  intro x τ hx
  simp [lookupTy] at hx

/-- Consing one binding preserves the pointwise correspondence: `lookupTy`
and `lookupVal` gate on the SAME condition `beqStr query key`. -/
theorem EnvTy_cons {env : Env} {Γ : TyCtx} {x : String} {v : Value} {τ : Ty}
    (hv : ValHasTy v τ) (henv : EnvTy env Γ) :
    EnvTy ((x, v) :: env) ((x, τ) :: Γ) := by
  intro y σ hy
  simp only [lookupTy] at hy
  simp only [lookupVal]
  split at hy
  · rename_i hb
    injection hy with h'
    rw [if_pos hb]
    exact ⟨v, rfl, h' ▸ hv⟩
  · rename_i hb
    rw [if_neg hb]
    exact henv y σ hy

/-- Typed argument values bind against the parameter list without an arity
error, and the resulting environment is typed by the parameter context. -/
theorem bindParams_sound : ∀ (ps : List (String × Ty)) (vs : List Value),
    ValsHasTy vs (ps.map (·.2)) →
    ∃ env', bindParams ps vs = some env' ∧ EnvTy env' ps := by
  intro ps
  induction ps with
  | nil =>
    intro vs hvs
    simp only [List.map_nil] at hvs
    cases hvs
    exact ⟨[], rfl, EnvTy_nil⟩
  | cons p ps ih =>
    intro vs hvs
    obtain ⟨x, τ⟩ := p
    simp only [List.map_cons] at hvs
    cases hvs with
    | @cons v _ vs' _ hv hrest =>
      obtain ⟨env', hbind, henv⟩ := ih vs' hrest
      refine ⟨(x, v) :: env', ?_, EnvTy_cons hv henv⟩
      simp only [bindParams, hbind]

/-! ## Operators cannot get stuck at agreeing types -/

theorem evalUnOp_sound {op : UnOp} {v : Value} (hv : ValHasTy v (unOpSig op).1) :
    ∃ w, evalUnOp op v = .ok w ∧ ValHasTy w (unOpSig op).2 := by
  cases op with
  | neg =>
    obtain ⟨n, rfl⟩ := hv.int_inv
    exact ⟨_, rfl, .vint _⟩
  | notB =>
    obtain ⟨b, rfl⟩ := hv.bool_inv
    exact ⟨_, rfl, .vbool _⟩

/-- At agreeing operand types `evalBinOp` never returns `stuckType`; the
only error left is `divByZero` (from `div`/`mod`). -/
theorem evalBinOp_sound {op : BinOp} {vl vr : Value}
    (hl : ValHasTy vl (binOpSig op).1) (hr : ValHasTy vr (binOpSig op).2.1) :
    evalBinOp op vl vr = .error .divByZero ∨
      ∃ w, evalBinOp op vl vr = .ok w ∧ ValHasTy w (binOpSig op).2.2 := by
  cases op with
  | add =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    exact Or.inr ⟨_, rfl, .vint _⟩
  | sub =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    exact Or.inr ⟨_, rfl, .vint _⟩
  | mul =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    exact Or.inr ⟨_, rfl, .vint _⟩
  | div =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    by_cases hb : b = 0
    · subst hb
      left
      simp [evalBinOp]
    · right
      exact ⟨.vint (a / b), by simp [evalBinOp, hb], .vint _⟩
  | mod =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    by_cases hb : b = 0
    · subst hb
      left
      simp [evalBinOp]
    · right
      exact ⟨.vint (a % b), by simp [evalBinOp, hb], .vint _⟩
  | lt =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    exact Or.inr ⟨_, rfl, .vbool _⟩
  | le =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    exact Or.inr ⟨_, rfl, .vbool _⟩
  | eqI =>
    obtain ⟨a, rfl⟩ := hl.int_inv
    obtain ⟨b, rfl⟩ := hr.int_inv
    exact Or.inr ⟨_, rfl, .vbool _⟩
  | eqB =>
    obtain ⟨a, rfl⟩ := hl.bool_inv
    obtain ⟨b, rfl⟩ := hr.bool_inv
    exact Or.inr ⟨_, rfl, .vbool _⟩
  | andB =>
    obtain ⟨a, rfl⟩ := hl.bool_inv
    obtain ⟨b, rfl⟩ := hr.bool_inv
    exact Or.inr ⟨_, rfl, .vbool _⟩
  | orB =>
    obtain ⟨a, rfl⟩ := hl.bool_inv
    obtain ⟨b, rfl⟩ := hr.bool_inv
    exact Or.inr ⟨_, rfl, .vbool _⟩

/-! ## The signature/table bridge (spec item 2)

Both `lookupSig` (typing side) and `assocLookup` (R6's model of the
function table) are first-match lookups keyed the same way: `beqStr f g`
is definitionally `cmpStr f g = .eq`. -/

theorem assocLookup_map_mem : ∀ (ds : List FunDef) (f : String) (d : FunDef),
    assocLookup (ds.map fun d => (d.name, d)) f = some d → d ∈ ds := by
  intro ds
  induction ds with
  | nil =>
    intro f d h
    simp [assocLookup] at h
  | cons d0 ds ih =>
    intro f d h
    simp only [List.map_cons, assocLookup] at h
    cases hc : cmpStr f d0.name with
    | eq =>
      rw [hc] at h
      dsimp only at h
      injection h with h'
      subst h'
      exact List.mem_cons.mpr (Or.inl rfl)
    | lt =>
      rw [hc] at h
      dsimp only at h
      exact List.mem_cons.mpr (Or.inr (ih f d h))
    | gt =>
      rw [hc] at h
      dsimp only at h
      exact List.mem_cons.mpr (Or.inr (ih f d h))

/-- `lookupSig` on the mapped signature list IS association lookup on the
mapped definition list, projected through `FunDef.sig`'s payload. -/
theorem lookupSig_eq_assocLookup : ∀ (ds : List FunDef) (f : String),
    lookupSig (ds.map FunDef.sig) f =
      (assocLookup (ds.map fun d => (d.name, d)) f).map
        (fun d => (d.params.map (·.2), d.retTy)) := by
  intro ds
  induction ds with
  | nil => intro f; rfl
  | cons d0 ds ih =>
    intro f
    simp only [List.map_cons, lookupSig, assocLookup, FunDef.sig]
    cases hc : cmpStr f d0.name with
    | eq =>
      have hb : beqStr f d0.name = true := by simp [beqStr, hc]
      rw [if_pos hb]
      rfl
    | lt =>
      have hb : beqStr f d0.name = false := by simp [beqStr, hc]
      rw [if_neg (by simp [hb])]
      exact ih f
    | gt =>
      have hb : beqStr f d0.name = false := by simp [beqStr, hc]
      rw [if_neg (by simp [hb])]
      exact ih f

/-- A typed call target exists in the function table, with matching
parameter types and return type (via R6 `find_fromList`). -/
theorem lookupSig_find? {ds : List FunDef} {f : String} {tys : List Ty} {ret : Ty}
    (h : lookupSig (ds.map FunDef.sig) f = some (tys, ret)) :
    ∃ d, RBNode.find? (mkFunTable ds) f = some d ∧ d ∈ ds ∧
      d.params.map (·.2) = tys ∧ d.retTy = ret := by
  have hEq : RBNode.find? (mkFunTable ds) f
      = assocLookup (ds.map fun d => (d.name, d)) f :=
    RBNode.find_fromList _ f
  rw [lookupSig_eq_assocLookup] at h
  cases ha : assocLookup (ds.map fun d => (d.name, d)) f with
  | none =>
    rw [ha] at h
    simp at h
  | some d =>
    rw [ha] at h
    simp only [Option.map] at h
    injection h with h'
    injection h' with h1 h2
    refine ⟨d, ?_, assocLookup_map_mem ds f d ha, h1, h2⟩
    rw [hEq, ha]

/-- Companion: an unknown call target is absent from the table too. -/
theorem lookupSig_none_find? {ds : List FunDef} {f : String}
    (h : lookupSig (ds.map FunDef.sig) f = none) :
    RBNode.find? (mkFunTable ds) f = none := by
  have hEq : RBNode.find? (mkFunTable ds) f
      = assocLookup (ds.map fun d => (d.name, d)) f :=
    RBNode.find_fromList _ f
  rw [lookupSig_eq_assocLookup] at h
  rw [hEq]
  cases ha : assocLookup (ds.map fun d => (d.name, d)) f with
  | none => rfl
  | some d =>
    rw [ha] at h
    simp at h

/-! ## L5 — type soundness -/

/-- Destructor for the soundness disjunction at an error outcome. -/
theorem okErr_of_error {α : Type} {P : α → Prop} {er : RtErr}
    (h : (∃ er', (Except.error er : Except RtErr α) = .error er' ∧ okErr er') ∨
         (∃ v, (Except.error er : Except RtErr α) = .ok v ∧ P v)) :
    okErr er := by
  rcases h with ⟨er', heq, hok⟩ | ⟨v, heq, -⟩
  · injection heq with h'
    rw [h']
    exact hok
  · exact nomatch heq

/-- Destructor for the soundness disjunction at a value outcome. -/
theorem pred_of_ok {α : Type} {P : α → Prop} {v : α}
    (h : (∃ er, (Except.ok v : Except RtErr α) = .error er ∧ okErr er) ∨
         (∃ w, (Except.ok v : Except RtErr α) = .ok w ∧ P w)) :
    P v := by
  rcases h with ⟨er, heq, -⟩ | ⟨w, heq, hw⟩
  · exact nomatch heq
  · injection heq with h'
    rw [h']
    exact hw

/-- Combined L5 for the mutual `eval`/`evalArgs` pair: under a well-typed
program, every defined outcome of a well-typed expression in a typed
environment is `divByZero` or a value of the static type. Induction on
fuel; the typing derivation is inverted by `cases`, the interpreter's
matches by the L4 one-layer discipline. -/
theorem eval_evalArgs_sound (p : Program) (hwt : WTProg p) (fuel : Nat) :
    (∀ (Γ : TyCtx) (env : Env) (e : Expr) (τ : Ty) (r : Except RtErr Value),
        HasType (p.funs.map FunDef.sig) Γ e τ → EnvTy env Γ →
        eval (mkFunTable p.funs) fuel env e = some r →
        (∃ er, r = .error er ∧ okErr er) ∨ (∃ v, r = .ok v ∧ ValHasTy v τ)) ∧
    (∀ (Γ : TyCtx) (env : Env) (as : Args) (tys : List Ty)
        (r : Except RtErr (List Value)),
        HasTypeArgs (p.funs.map FunDef.sig) Γ as tys → EnvTy env Γ →
        evalArgs (mkFunTable p.funs) fuel env as = some r →
        (∃ er, r = .error er ∧ okErr er) ∨ (∃ vs, r = .ok vs ∧ ValsHasTy vs tys)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro Γ env e τ r _ _ h
      simp [eval] at h
    · intro Γ env as tys r _ _ h
      simp [evalArgs] at h
  | succ f ih =>
    obtain ⟨ihe, iha⟩ := ih
    refine ⟨?_, ?_⟩
    · intro Γ env e τ r ht henv h
      cases ht with
      | intLit _ n =>
        rw [eval.eq_def] at h
        dsimp only at h
        injection h with h'
        exact Or.inr ⟨.vint n, h'.symm, .vint n⟩
      | boolLit _ b =>
        rw [eval.eq_def] at h
        dsimp only at h
        injection h with h'
        exact Or.inr ⟨.vbool b, h'.symm, .vbool b⟩
      | var _ x τx hx =>
        rw [eval.eq_def] at h
        dsimp only at h
        obtain ⟨v, hv, hvt⟩ := henv x _ hx
        rw [hv] at h
        dsimp only at h
        injection h with h'
        exact Or.inr ⟨v, h'.symm, hvt⟩
      | unop _ op e1 he =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hx : eval (mkFunTable p.funs) f env e1 with
        | none =>
          rw [hx] at h
          simp at h
        | some ve =>
          rw [hx] at h
          cases ve with
          | error er =>
            dsimp only at h
            injection h with h'
            exact Or.inl
              ⟨er, h'.symm, okErr_of_error (ihe Γ env e1 _ (.error er) he henv hx)⟩
          | ok v =>
            have hv := pred_of_ok (ihe Γ env e1 _ (.ok v) he henv hx)
            dsimp only at h
            injection h with h'
            obtain ⟨w, hw, hwt'⟩ := evalUnOp_sound hv
            exact Or.inr ⟨w, by rw [← h', hw], hwt'⟩
      | binop _ op l1 r1 hl1 hr1 =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hx : eval (mkFunTable p.funs) f env l1 with
        | none =>
          rw [hx] at h
          simp at h
        | some vl =>
          rw [hx] at h
          cases vl with
          | error er =>
            dsimp only at h
            injection h with h'
            exact Or.inl
              ⟨er, h'.symm, okErr_of_error (ihe Γ env l1 _ (.error er) hl1 henv hx)⟩
          | ok v1 =>
            have hv1 := pred_of_ok (ihe Γ env l1 _ (.ok v1) hl1 henv hx)
            dsimp only at h
            cases hy : eval (mkFunTable p.funs) f env r1 with
            | none =>
              rw [hy] at h
              simp at h
            | some vr =>
              rw [hy] at h
              cases vr with
              | error er =>
                dsimp only at h
                injection h with h'
                exact Or.inl
                  ⟨er, h'.symm, okErr_of_error (ihe Γ env r1 _ (.error er) hr1 henv hy)⟩
              | ok v2 =>
                have hv2 := pred_of_ok (ihe Γ env r1 _ (.ok v2) hr1 henv hy)
                dsimp only at h
                injection h with h'
                rcases evalBinOp_sound hv1 hv2 with hdiv | ⟨w, hw, hwt'⟩
                · exact Or.inl ⟨.divByZero, by rw [← h', hdiv], rfl⟩
                · exact Or.inr ⟨w, by rw [← h', hw], hwt'⟩
      | ite _ c t1 e1 τ' hc ht1 he1 =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hx : eval (mkFunTable p.funs) f env c with
        | none =>
          rw [hx] at h
          simp at h
        | some vc =>
          rw [hx] at h
          cases vc with
          | error er =>
            dsimp only at h
            injection h with h'
            exact Or.inl
              ⟨er, h'.symm, okErr_of_error (ihe Γ env c _ (.error er) hc henv hx)⟩
          | ok v =>
            have hv := pred_of_ok (ihe Γ env c _ (.ok v) hc henv hx)
            obtain ⟨b, rfl⟩ := hv.bool_inv
            dsimp only at h
            cases b with
            | true =>
              simp at h
              exact ihe Γ env t1 _ r ht1 henv h
            | false =>
              simp at h
              exact ihe Γ env e1 _ r he1 henv h
      | letE _ x bound body τ₁ τ₂ hb1 hb2 =>
        rw [eval.eq_def] at h
        dsimp only at h
        cases hx : eval (mkFunTable p.funs) f env bound with
        | none =>
          rw [hx] at h
          simp at h
        | some vb =>
          rw [hx] at h
          cases vb with
          | error er =>
            dsimp only at h
            injection h with h'
            exact Or.inl
              ⟨er, h'.symm, okErr_of_error (ihe Γ env bound _ (.error er) hb1 henv hx)⟩
          | ok v =>
            have hv := pred_of_ok (ihe Γ env bound _ (.ok v) hb1 henv hx)
            dsimp only at h
            exact ihe ((x, τ₁) :: Γ) ((x, v) :: env) body _ r hb2
              (EnvTy_cons hv henv) h
      | call _ fn args tys ret hf hargs =>
        rw [eval.eq_def] at h
        dsimp only at h
        obtain ⟨d, hfind, hmem, hptys, hret⟩ := lookupSig_find? hf
        rw [hfind] at h
        dsimp only at h
        cases ha : evalArgs (mkFunTable p.funs) f env args with
        | none =>
          rw [ha] at h
          simp at h
        | some va =>
          rw [ha] at h
          cases va with
          | error er =>
            dsimp only at h
            injection h with h'
            exact Or.inl
              ⟨er, h'.symm, okErr_of_error (iha Γ env args tys (.error er) hargs henv ha)⟩
          | ok vs =>
            have hvs := pred_of_ok (iha Γ env args tys (.ok vs) hargs henv ha)
            rw [← hptys] at hvs
            obtain ⟨env', hbind, henv'⟩ := bindParams_sound d.params vs hvs
            dsimp only at h
            rw [hbind] at h
            dsimp only at h
            have hbody := hwt.bodies d hmem
            have hres := ihe d.params env' d.body d.retTy r hbody henv' h
            rw [hret] at hres
            exact hres
    · intro Γ env as tys r hta henv h
      cases hta with
      | nil _ =>
        rw [evalArgs.eq_def] at h
        dsimp only at h
        injection h with h'
        exact Or.inr ⟨[], h'.symm, .nil⟩
      | cons _ e1 rest τ1 tys1 h1 hrest =>
        rw [evalArgs.eq_def] at h
        dsimp only at h
        cases hx : eval (mkFunTable p.funs) f env e1 with
        | none =>
          rw [hx] at h
          simp at h
        | some ve =>
          rw [hx] at h
          cases ve with
          | error er =>
            dsimp only at h
            injection h with h'
            exact Or.inl
              ⟨er, h'.symm, okErr_of_error (ihe Γ env e1 _ (.error er) h1 henv hx)⟩
          | ok v =>
            have hv := pred_of_ok (ihe Γ env e1 _ (.ok v) h1 henv hx)
            dsimp only at h
            cases hy : evalArgs (mkFunTable p.funs) f env rest with
            | none =>
              rw [hy] at h
              simp at h
            | some vrest =>
              rw [hy] at h
              cases vrest with
              | error er =>
                dsimp only at h
                injection h with h'
                exact Or.inl
                  ⟨er, h'.symm,
                    okErr_of_error (iha Γ env rest tys1 (.error er) hrest henv hy)⟩
              | ok vs =>
                have hvs := pred_of_ok (iha Γ env rest tys1 (.ok vs) hrest henv hy)
                dsimp only at h
                injection h with h'
                exact Or.inr ⟨v :: vs, h'.symm, .cons hv hvs⟩

/-- **L5** — TYPE SOUNDNESS. A well-typed expression of a well-typed
program cannot get stuck: every defined interpreter outcome is either the
allowed `divByZero` error or a value of the expression's static type. -/
theorem eval_sound {p : Program} {Γ : TyCtx} {env : Env} {e : Expr} {τ : Ty}
    {fuel : Nat} {r : Except RtErr Value}
    (hwt : WTProg p) (ht : HasType (p.funs.map FunDef.sig) Γ e τ)
    (henv : EnvTy env Γ) (h : eval (mkFunTable p.funs) fuel env e = some r) :
    (∃ er, r = .error er ∧ okErr er) ∨ (∃ v, r = .ok v ∧ ValHasTy v τ) :=
  (eval_evalArgs_sound p hwt fuel).1 Γ env e τ r ht henv h

/-- L5, argument-list companion. -/
theorem evalArgs_sound {p : Program} {Γ : TyCtx} {env : Env} {as : Args}
    {tys : List Ty} {fuel : Nat} {r : Except RtErr (List Value)}
    (hwt : WTProg p) (hta : HasTypeArgs (p.funs.map FunDef.sig) Γ as tys)
    (henv : EnvTy env Γ) (h : evalArgs (mkFunTable p.funs) fuel env as = some r) :
    (∃ er, r = .error er ∧ okErr er) ∨ (∃ vs, r = .ok vs ∧ ValsHasTy vs tys) :=
  (eval_evalArgs_sound p hwt fuel).2 Γ env as tys r hta henv h

/-- Program-level corollary through the verified typechecker: a program
accepted by `checkProgram` at type `τ` can only produce `divByZero` or a
value of type `τ`. -/
theorem runProgram_sound {p : Program} {τ : Ty} {fuel : Nat}
    {r : Except RtErr Value}
    (hc : checkProgram p = .ok τ) (h : runProgram p fuel = some r) :
    r = .error .divByZero ∨ ∃ v, r = .ok v ∧ ValHasTy v τ := by
  have hwt : WTProg p := checkProgram_sound p τ hc
  have hmain : HasType (p.funs.map FunDef.sig) [] p.main τ := by
    simp only [checkProgram] at hc
    split at hc
    · exact nomatch hc
    · exact typecheck_sound _ [] p.main τ hc
  rcases eval_sound hwt hmain EnvTy_nil h with ⟨er, hr, hok⟩ | hv
  · have hok' : er = RtErr.divByZero := hok
    left
    rw [hr, hok']
  · exact Or.inr hv

/-! ## O3 — whole-program optimization preserves defined outcomes -/

theorem optFun_name (d : FunDef) : (optFun d).name = d.name := rfl

/-- Mapping `optFun` commutes with first-match association lookup:
`optFun` preserves the key (`name`). -/
theorem assocLookup_map_optFun : ∀ (ds : List FunDef) (f : String),
    assocLookup ((ds.map optFun).map fun d => (d.name, d)) f =
      (assocLookup (ds.map fun d => (d.name, d)) f).map optFun := by
  intro ds
  induction ds with
  | nil => intro f; rfl
  | cons d0 ds ih =>
    intro f
    simp only [List.map_cons, assocLookup, optFun_name]
    cases hc : cmpStr f d0.name with
    | eq => rfl
    | lt => exact ih f
    | gt => exact ih f

/-- The body-optimized function table is the `optFun`-image of the
original, lookup by lookup (R6 on both sides + the list lemma above). -/
theorem find?_mkFunTable_opt (ds : List FunDef) (f : String) :
    RBNode.find? (mkFunTable (ds.map optFun)) f =
      (RBNode.find? (mkFunTable ds) f).map optFun := by
  have h1 : RBNode.find? (mkFunTable (ds.map optFun)) f
      = assocLookup ((ds.map optFun).map fun d => (d.name, d)) f :=
    RBNode.find_fromList _ f
  have h2 : RBNode.find? (mkFunTable ds) f
      = assocLookup (ds.map fun d => (d.name, d)) f :=
    RBNode.find_fromList _ f
  rw [h1, h2]
  exact assocLookup_map_optFun ds f

/-- Table-aware O2: evaluating the folded expression under the
body-optimized table preserves every defined outcome at the SAME fuel.
Mirrors `optExpr_optArgs_eval` (O2); the one new step is the call case,
which rewrites the table lookup through `find?_mkFunTable_opt` and applies
the IH to the callee's optimized body (`(optFun d).body = optExpr d.body`). -/
theorem eval_evalArgs_opt_table (ds : List FunDef) (f : Nat) :
    (∀ (env : Env) (e : Expr) (res : Except RtErr Value),
        eval (mkFunTable ds) f env e = some res →
        eval (mkFunTable (ds.map optFun)) f env (optExpr e) = some res) ∧
    (∀ (env : Env) (as : Args) (res : Except RtErr (List Value)),
        evalArgs (mkFunTable ds) f env as = some res →
        evalArgs (mkFunTable (ds.map optFun)) f env (optArgs as) = some res) := by
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
        simp only [optExpr]
        exact h
      | boolLit b =>
        simp only [optExpr]
        exact h
      | var x =>
        simp only [optExpr]
        exact h
      | unop op e1 =>
        simp only [optExpr]
        apply foldUnOp_eval
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hx : eval (mkFunTable ds) f env e1 with
        | none =>
          rw [hx] at h
          simp at h
        | some v =>
          rw [hx] at h
          rw [ihe env e1 v hx]
          exact h
      | binop op l r =>
        simp only [optExpr]
        apply foldBinOp_eval
        rw [eval.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hl : eval (mkFunTable ds) f env l with
        | none =>
          rw [hl] at h
          simp at h
        | some vl =>
          rw [hl] at h
          rw [ihe env l vl hl]
          cases vl with
          | error er => exact h
          | ok v =>
            dsimp only at h ⊢
            cases hr : eval (mkFunTable ds) f env r with
            | none =>
              rw [hr] at h
              simp at h
            | some vr =>
              rw [hr] at h
              rw [ihe env r vr hr]
              exact h
      | ite c t e1 =>
        simp only [optExpr]
        rw [eval.eq_def] at h
        dsimp only at h
        cases hc : eval (mkFunTable ds) f env c with
        | none =>
          rw [hc] at h
          simp at h
        | some vc =>
          rw [hc] at h
          have hc' : eval (mkFunTable (ds.map optFun)) f env (optExpr c) = some vc :=
            ihe env c vc hc
          split
          · rename_i heq
            rw [heq] at hc'
            cases eval_boolLit_inv hc'
            simp at h
            exact eval_mono (ihe env t res h)
          · rename_i heq
            rw [heq] at hc'
            cases eval_boolLit_inv hc'
            simp at h
            exact eval_mono (ihe env e1 res h)
          · rw [eval.eq_def]
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
        cases hb : eval (mkFunTable ds) f env bound with
        | none =>
          rw [hb] at h
          simp at h
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
        cases hf : RBNode.find? (mkFunTable ds) fn with
        | none =>
          rw [hf] at h
          have hf' : RBNode.find? (mkFunTable (ds.map optFun)) fn = none := by
            simp [find?_mkFunTable_opt, hf]
          rw [hf']
          exact h
        | some d =>
          rw [hf] at h
          have hf' : RBNode.find? (mkFunTable (ds.map optFun)) fn
              = some (optFun d) := by
            simp [find?_mkFunTable_opt, hf]
          rw [hf']
          dsimp only [optFun] at h ⊢
          cases ha : evalArgs (mkFunTable ds) f env args with
          | none =>
            rw [ha] at h
            simp at h
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
        simp only [optArgs]
        exact h
      | cons e1 rest =>
        simp only [optArgs]
        rw [evalArgs.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hx : eval (mkFunTable ds) f env e1 with
        | none =>
          rw [hx] at h
          simp at h
        | some v =>
          rw [hx] at h
          rw [ihe env e1 v hx]
          cases v with
          | error er => exact h
          | ok vv =>
            dsimp only at h ⊢
            cases hr : evalArgs (mkFunTable ds) f env rest with
            | none =>
              rw [hr] at h
              simp at h
            | some vr =>
              rw [hr] at h
              rw [iha env rest vr hr]
              exact h

/-- **O3** — whole-program constant folding preserves every defined
outcome at the same fuel: optimized main under the optimized table. -/
theorem optProgram_run {p : Program} {fuel : Nat} {r : Except RtErr Value}
    (h : runProgram p fuel = some r) : runProgram (optProgram p) fuel = some r :=
  (eval_evalArgs_opt_table p.funs fuel).1 [] p.main r h

end Shallot
