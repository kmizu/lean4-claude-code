import Shallot.Lang.Ast

/-!
# Typing relation (the SPECIFICATION)

Syntax-directed inductive typing judgment. One rule per constructor;
operator typing is factored through `binOpSig`/`unOpSig` so there is ONE
binop rule, not eleven. The executable `typecheck` (Lang/TypeCheck.lean) is
proven sound AND complete w.r.t. this relation in M6.
-/

namespace Shallot

/-- Function signatures: name ↦ (parameter types, return type). -/
abbrev Sig := List (String × (List Ty × Ty))

/-- Typing context for local variables (cons = shadowing, like `let`). -/
abbrev TyCtx := List (String × Ty)

def lookupTy : TyCtx → String → Option Ty
  | [], _ => none
  | (y, τ) :: rest, x => if beqStr x y then some τ else lookupTy rest x

def lookupSig : Sig → String → Option (List Ty × Ty)
  | [], _ => none
  | (g, s) :: rest, f => if beqStr f g then some s else lookupSig rest f

/-- (left operand, right operand, result). -/
def binOpSig : BinOp → Ty × Ty × Ty
  | .add | .sub | .mul | .div | .mod => (.int, .int, .int)
  | .lt | .le | .eqI => (.int, .int, .bool)
  | .eqB | .andB | .orB => (.bool, .bool, .bool)

def unOpSig : UnOp → Ty × Ty
  | .neg => (.int, .int)
  | .notB => (.bool, .bool)

mutual
  inductive HasType (S : Sig) : TyCtx → Expr → Ty → Prop where
    | intLit (Γ : TyCtx) (n : Int) : HasType S Γ (.intLit n) .int
    | boolLit (Γ : TyCtx) (b : Bool) : HasType S Γ (.boolLit b) .bool
    | var (Γ : TyCtx) (x : String) (τ : Ty) (h : lookupTy Γ x = some τ) :
        HasType S Γ (.var x) τ
    | unop (Γ : TyCtx) (op : UnOp) (e : Expr)
        (h : HasType S Γ e (unOpSig op).1) :
        HasType S Γ (.unop op e) (unOpSig op).2
    | binop (Γ : TyCtx) (op : BinOp) (l r : Expr)
        (hl : HasType S Γ l (binOpSig op).1)
        (hr : HasType S Γ r (binOpSig op).2.1) :
        HasType S Γ (.binop op l r) (binOpSig op).2.2
    | ite (Γ : TyCtx) (c t e : Expr) (τ : Ty)
        (hc : HasType S Γ c .bool)
        (ht : HasType S Γ t τ)
        (he : HasType S Γ e τ) :
        HasType S Γ (.ite c t e) τ
    | letE (Γ : TyCtx) (x : String) (bound body : Expr) (τ₁ τ₂ : Ty)
        (h₁ : HasType S Γ bound τ₁)
        (h₂ : HasType S ((x, τ₁) :: Γ) body τ₂) :
        HasType S Γ (.letE x bound body) τ₂
    | call (Γ : TyCtx) (f : String) (args : Args) (tys : List Ty) (ret : Ty)
        (hf : lookupSig S f = some (tys, ret))
        (hargs : HasTypeArgs S Γ args tys) :
        HasType S Γ (.call f args) ret
  inductive HasTypeArgs (S : Sig) : TyCtx → Args → List Ty → Prop where
    | nil (Γ : TyCtx) : HasTypeArgs S Γ .nil []
    | cons (Γ : TyCtx) (e : Expr) (rest : Args) (τ : Ty) (tys : List Ty)
        (h : HasType S Γ e τ)
        (hr : HasTypeArgs S Γ rest tys) :
        HasTypeArgs S Γ (.cons e rest) (τ :: tys)
end

/-- A function's signature entry. -/
def FunDef.sig (d : FunDef) : String × (List Ty × Ty) :=
  (d.name, (d.params.map (·.2), d.retTy))

/-- The program-level judgment: every body well-typed under the full
signature table (mutual recursion by construction), `main` well-typed.

Duplicate function/parameter names are NOT ruled out: lookups take the
first match consistently in the typechecker, the interpreter and the VM,
so shadowed entries are simply dead — and the proofs stay lighter. -/
structure WTProg (p : Program) : Prop where
  bodies : ∀ d, d ∈ p.funs →
    HasType (p.funs.map FunDef.sig) d.params d.body d.retTy
  main : ∃ τ, HasType (p.funs.map FunDef.sig) [] p.main τ

end Shallot
