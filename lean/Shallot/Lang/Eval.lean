import Shallot.Lang.Ast
import Shallot.Lang.Typing

/-!
# Fuel-based interpreter

Project-wide conventions (plan D7/D14): every recursive call decrements
fuel; `none` means "out of fuel" and NOTHING else; `some (.error _)` is a
semantic outcome. Error taxonomy: `stuck*` errors are provably absent for
well-typed programs (type soundness L5, M8); `divByZero` is allowed.

The function table is the verified `RBNode` map — its `find_fromList` model
theorem (R6) is what connects table lookups back to the signature list used
by the typing relation.
-/

namespace Shallot

inductive Value where
  | vint (n : Int)
  | vbool (b : Bool)

inductive RtErr where
  | stuckUnbound (x : String)
  | stuckFun (f : String)
  | stuckArity (f : String)
  | stuckType
  | stuckVM
  | divByZero

def RtErr.render : RtErr → String
  | .stuckUnbound x => "StuckUnbound:" ++ x
  | .stuckFun f => "StuckFun:" ++ f
  | .stuckArity f => "StuckArity:" ++ f
  | .stuckType => "StuckType"
  | .stuckVM => "StuckVM"
  | .divByZero => "DivByZero"

abbrev Env := List (String × Value)

def lookupVal : Env → String → Option Value
  | [], _ => none
  | (y, v) :: rest, x => if beqStr x y then some v else lookupVal rest x

/-- Bind parameters to argument values; `none` on arity mismatch. -/
def bindParams : List (String × Ty) → List Value → Option Env
  | [], [] => some []
  | [], _ :: _ => none
  | _ :: _, [] => none
  | (x, _) :: ps, v :: vs =>
    match bindParams ps vs with
    | some env => some ((x, v) :: env)
    | none => none

def evalUnOp : UnOp → Value → Except RtErr Value
  | .neg, .vint n => .ok (.vint (-n))
  | .notB, .vbool b => .ok (.vbool (if b = true then false else true))
  | _, _ => .error .stuckType

def evalBinOp : BinOp → Value → Value → Except RtErr Value
  | .add, .vint a, .vint b => .ok (.vint (a + b))
  | .sub, .vint a, .vint b => .ok (.vint (a - b))
  | .mul, .vint a, .vint b => .ok (.vint (a * b))
  | .div, .vint a, .vint b =>
    if b = 0 then .error .divByZero else .ok (.vint (a / b))
  | .mod, .vint a, .vint b =>
    if b = 0 then .error .divByZero else .ok (.vint (a % b))
  | .lt, .vint a, .vint b => .ok (.vbool (if a < b then true else false))
  | .le, .vint a, .vint b => .ok (.vbool (if a ≤ b then true else false))
  | .eqI, .vint a, .vint b => .ok (.vbool (if a = b then true else false))
  | .eqB, .vbool a, .vbool b => .ok (.vbool (if a = b then true else false))
  | .andB, .vbool a, .vbool b => .ok (.vbool (if a = true then b else false))
  | .orB, .vbool a, .vbool b => .ok (.vbool (if a = true then true else b))
  | _, _, _ => .error .stuckType

mutual
  def eval (ft : RBNode FunDef) : Nat → Env → Expr → Option (Except RtErr Value)
    | 0, _, _ => none
    | _ + 1, _, .intLit n => some (.ok (.vint n))
    | _ + 1, _, .boolLit b => some (.ok (.vbool b))
    | _ + 1, env, .var x =>
      match lookupVal env x with
      | some v => some (.ok v)
      | none => some (.error (.stuckUnbound x))
    | fuel + 1, env, .unop op e =>
      match eval ft fuel env e with
      | none => none
      | some (.error er) => some (.error er)
      | some (.ok v) => some (evalUnOp op v)
    | fuel + 1, env, .binop op l r =>
      match eval ft fuel env l with
      | none => none
      | some (.error er) => some (.error er)
      | some (.ok vl) =>
        match eval ft fuel env r with
        | none => none
        | some (.error er) => some (.error er)
        | some (.ok vr) => some (evalBinOp op vl vr)
    | fuel + 1, env, .ite c t e =>
      match eval ft fuel env c with
      | none => none
      | some (.error er) => some (.error er)
      | some (.ok (.vbool b)) =>
        if b = true then eval ft fuel env t else eval ft fuel env e
      | some (.ok _) => some (.error .stuckType)
    | fuel + 1, env, .letE x bound body =>
      match eval ft fuel env bound with
      | none => none
      | some (.error er) => some (.error er)
      | some (.ok v) => eval ft fuel ((x, v) :: env) body
    | fuel + 1, env, .call f args =>
      match RBNode.find? ft f with
      | none => some (.error (.stuckFun f))
      | some d =>
        match evalArgs ft fuel env args with
        | none => none
        | some (.error er) => some (.error er)
        | some (.ok vs) =>
          match bindParams d.params vs with
          | none => some (.error (.stuckArity f))
          | some env' => eval ft fuel env' d.body

  def evalArgs (ft : RBNode FunDef) : Nat → Env → Args → Option (Except RtErr (List Value))
    | 0, _, _ => none
    | _ + 1, _, .nil => some (.ok [])
    | fuel + 1, env, .cons e rest =>
      match eval ft fuel env e with
      | none => none
      | some (.error er) => some (.error er)
      | some (.ok v) =>
        match evalArgs ft fuel env rest with
        | none => none
        | some (.error er) => some (.error er)
        | some (.ok vs) => some (.ok (v :: vs))
end

def mkFunTable (funs : List FunDef) : RBNode FunDef :=
  RBNode.fromList (funs.map fun d => (d.name, d))

def runProgram (p : Program) (fuel : Nat) : Option (Except RtErr Value) :=
  eval (mkFunTable p.funs) fuel [] p.main

end Shallot
