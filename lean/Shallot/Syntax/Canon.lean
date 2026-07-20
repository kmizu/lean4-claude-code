import Shallot.Syntax.Grammar
import Shallot.Lang.Ast

/-!
# Printer-normal (canonical) ASTs

The roundtrip theorem's hypothesis: identifiers are valid non-keywords, and
no `.unop .neg (.intLit _)` node exists (the printer renders negative
literals as `( - digits )`, which `treeToAst` normalizes back). This file
is proof-side only — it is NOT extracted, so stdlib helpers are fine.
-/

namespace Shallot

def keywords : List String :=
  ["if", "then", "else", "let", "in", "def", "true", "false", "int", "bool"]

def isIdStartB (c : Char) : Bool :=
  (leChar 'a' c && leChar c 'z') || (leChar 'A' c && leChar c 'Z') || beqChar c '_'

def isIdContB (c : Char) : Bool :=
  isIdStartB c || (leChar '0' c && leChar c '9')

def validIdentB (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdStartB c && cs.all isIdContB && !(keywords.contains s)

mutual
  def canonExpr : Expr → Bool
    | .intLit _ => true
    | .boolLit _ => true
    | .var x => validIdentB x
    | .unop .neg (.intLit _) => false -- printer-normal form violation
    | .unop _ e => canonExpr e
    | .binop _ l r => canonExpr l && canonExpr r
    | .ite c t e => canonExpr c && canonExpr t && canonExpr e
    | .letE x bound body => validIdentB x && canonExpr bound && canonExpr body
    | .call f args => validIdentB f && canonArgs args

  def canonArgs : Args → Bool
    | .nil => true
    | .cons e rest => canonExpr e && canonArgs rest
end

def canonFun (d : FunDef) : Bool :=
  validIdentB d.name && d.params.all (fun p => validIdentB p.1) && canonExpr d.body

def canonProgram (p : Program) : Bool :=
  p.funs.all canonFun && canonExpr p.main

end Shallot
