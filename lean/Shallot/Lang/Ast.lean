import Shallot.Data.RBMap

/-!
# Shallot language — abstract syntax

First-order functional language (no first-class functions — the deliberate
scope that keeps compiler correctness fully provable): Int/Bool types,
literals, unary/binary operators, if, let, and calls to top-level mutually
recursive functions.

Design (plan D8): argument lists are a hand-rolled mutual `Expr`/`Args`
pair, NOT `List Expr` — nested inductives have awkward recursors in bare
Lean 4; the mutual pair gives clean mutual induction and extracts to two
sealed traits.

Equality on custom types is via hand-written `beq*` functions (extractable
subset: no derived `DecidableEq` in executable paths).
-/

namespace Shallot

inductive Ty where
  | int
  | bool

def Ty.beq : Ty → Ty → Bool
  | .int, .int => true
  | .bool, .bool => true
  | _, _ => false

def beqStr (a b : String) : Bool :=
  match cmpStr a b with
  | .eq => true
  | _ => false

inductive UnOp where
  | neg
  | notB

inductive BinOp where
  | add | sub | mul | div | mod
  | lt | le | eqI | eqB
  | andB | orB

mutual
  inductive Expr where
    | intLit (n : Int)
    | boolLit (b : Bool)
    | var (x : String)
    | unop (op : UnOp) (e : Expr)
    | binop (op : BinOp) (l r : Expr)
    | ite (c t e : Expr)
    | letE (x : String) (bound body : Expr)
    | call (f : String) (args : Args)
  inductive Args where
    | nil
    | cons (e : Expr) (rest : Args)
end

def Args.toList : Args → List Expr
  | .nil => []
  | .cons e rest => e :: rest.toList

structure FunDef where
  name : String
  params : List (String × Ty)
  retTy : Ty
  body : Expr

structure Program where
  funs : List FunDef
  main : Expr

end Shallot
