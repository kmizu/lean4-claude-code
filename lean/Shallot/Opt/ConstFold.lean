import Shallot.Lang.Eval

/-!
# Constant-folding optimizer

Bottom-up folding of literal operations and known-condition `if`s. Division
and modulo fold ONLY when the divisor literal is nonzero — a folded
`divByZero` would change observable behavior (semantic preservation O2, M8).
No `let`-inlining (needs a substitution lemma — widening item W6).
-/

namespace Shallot

def foldBinOp (op : BinOp) (l r : Expr) : Expr :=
  match op, l, r with
  | .add, .intLit a, .intLit b => .intLit (a + b)
  | .sub, .intLit a, .intLit b => .intLit (a - b)
  | .mul, .intLit a, .intLit b => .intLit (a * b)
  | .div, .intLit a, .intLit b =>
    if b = 0 then .binop .div (.intLit a) (.intLit b) else .intLit (a / b)
  | .mod, .intLit a, .intLit b =>
    if b = 0 then .binop .mod (.intLit a) (.intLit b) else .intLit (a % b)
  | .lt, .intLit a, .intLit b => .boolLit (if a < b then true else false)
  | .le, .intLit a, .intLit b => .boolLit (if a ≤ b then true else false)
  | .eqI, .intLit a, .intLit b => .boolLit (if a = b then true else false)
  | .eqB, .boolLit a, .boolLit b => .boolLit (if a = b then true else false)
  | .andB, .boolLit a, .boolLit b => .boolLit (if a = true then b else false)
  | .orB, .boolLit a, .boolLit b => .boolLit (if a = true then true else b)
  | op, l, r => .binop op l r

def foldUnOp (op : UnOp) (e : Expr) : Expr :=
  match op, e with
  | .neg, .intLit n => .intLit (-n)
  | .notB, .boolLit b => .boolLit (if b = true then false else true)
  | op, e => .unop op e

mutual
  def optExpr : Expr → Expr
    | .intLit n => .intLit n
    | .boolLit b => .boolLit b
    | .var x => .var x
    | .unop op e => foldUnOp op (optExpr e)
    | .binop op l r => foldBinOp op (optExpr l) (optExpr r)
    | .ite c t e =>
      match optExpr c with
      | .boolLit true => optExpr t
      | .boolLit false => optExpr e
      | c' => .ite c' (optExpr t) (optExpr e)
    | .letE x bound body => .letE x (optExpr bound) (optExpr body)
    | .call f args => .call f (optArgs args)

  def optArgs : Args → Args
    | .nil => .nil
    | .cons e rest => .cons (optExpr e) (optArgs rest)
end

def optFun (d : FunDef) : FunDef :=
  { d with body := optExpr d.body }

def optProgram (p : Program) : Program :=
  { funs := p.funs.map optFun, main := optExpr p.main }

end Shallot
