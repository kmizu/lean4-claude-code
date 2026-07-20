import Shallot.Lang.Typing

/-!
# Executable typechecker

Structural mutual recursion (no fuel needed). Written with EXPLICIT `match`
on `Except` results rather than `do`-notation: monadic bind would drag
typeclass machinery into the extraction closure; explicit matches extract
today via nested-matcher decomposition (v2).

Proven sound AND complete w.r.t. `HasType` in M6 (L1/L2/L3).
-/

namespace Shallot

inductive TypeError where
  | unboundVar (x : String)
  | unknownFun (f : String)
  | arityMismatch (f : String)
  | typeMismatch

def TypeError.render : TypeError → String
  | .unboundVar x => "UnboundVar:" ++ x
  | .unknownFun f => "UnknownFun:" ++ f
  | .arityMismatch f => "ArityMismatch:" ++ f
  | .typeMismatch => "TypeMismatch"

mutual
  def typecheck (S : Sig) (Γ : TyCtx) : Expr → Except TypeError Ty
    | .intLit _ => .ok .int
    | .boolLit _ => .ok .bool
    | .var x =>
      match lookupTy Γ x with
      | some τ => .ok τ
      | none => .error (.unboundVar x)
    | .unop op e =>
      match typecheck S Γ e with
      | .error er => .error er
      | .ok τ =>
        if Ty.beq τ (unOpSig op).1 then .ok (unOpSig op).2
        else .error .typeMismatch
    | .binop op l r =>
      match typecheck S Γ l with
      | .error er => .error er
      | .ok τl =>
        match typecheck S Γ r with
        | .error er => .error er
        | .ok τr =>
          if Ty.beq τl (binOpSig op).1 then
            if Ty.beq τr (binOpSig op).2.1 then .ok (binOpSig op).2.2
            else .error .typeMismatch
          else .error .typeMismatch
    | .ite c t e =>
      match typecheck S Γ c with
      | .error er => .error er
      | .ok τc =>
        if Ty.beq τc .bool then
          match typecheck S Γ t with
          | .error er => .error er
          | .ok τt =>
            match typecheck S Γ e with
            | .error er => .error er
            | .ok τe =>
              if Ty.beq τt τe then .ok τt else .error .typeMismatch
        else .error .typeMismatch
    | .letE x bound body =>
      match typecheck S Γ bound with
      | .error er => .error er
      | .ok τ₁ => typecheck S ((x, τ₁) :: Γ) body
    | .call f args =>
      match lookupSig S f with
      | none => .error (.unknownFun f)
      | some (tys, ret) =>
        match typecheckArgs S Γ f args tys with
        | .error er => .error er
        | .ok _ => .ok ret

  def typecheckArgs (S : Sig) (Γ : TyCtx) (f : String) :
      Args → List Ty → Except TypeError Unit
    | .nil, [] => .ok ()
    | .nil, _ :: _ => .error (.arityMismatch f)
    | .cons _ _, [] => .error (.arityMismatch f)
    | .cons e rest, τ :: tys =>
      match typecheck S Γ e with
      | .error er => .error er
      | .ok τe =>
        if Ty.beq τe τ then typecheckArgs S Γ f rest tys
        else .error .typeMismatch
end

/-- Whole-program check: every body against the full signature table, then
`main`. Returns `main`'s type. -/
def checkFuns (S : Sig) : List FunDef → Except TypeError Unit
  | [] => .ok ()
  | d :: rest =>
    match typecheck S d.params d.body with
    | .error er => .error er
    | .ok τ =>
      if Ty.beq τ d.retTy then checkFuns S rest
      else .error .typeMismatch

def checkProgram (p : Program) : Except TypeError Ty :=
  let S := p.funs.map FunDef.sig
  match checkFuns S p.funs with
  | .error er => .error er
  | .ok _ => typecheck S [] p.main

end Shallot
