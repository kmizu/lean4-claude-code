import Shallot.Lang.Ast
import Shallot.Render

/-!
# Canonical printer

Machine-oriented canonical form (pretty-printing is widening item W4):
- every token is emitted with ONE trailing space, so every token boundary
  in printed output is a space — the roundtrip lemmas' follow-set side
  conditions collapse to "next char is a space or EOF"
- every compound expression is fully parenthesized; atoms are bare
- negative literals print as `( - digits )`; `treeToAst` normalizes the
  parsed `unop neg (intLit k)` back to `intLit (-k)` — hence the `Canon`
  hypothesis on roundtrip (no `.unop .neg (.intLit _)` nodes in the AST)
-/

namespace Shallot

/-- Own decimal digits (fuel = value bound): `Nat.repr` is an extraction
BUILTIN whose inverse cannot be reasoned about — this one has equations,
and `digitsVal_natDigits` (roundtrip layer 1) proves the inverse. -/
def natDigitsGo : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d := Char.ofNat ('0'.toNat + n % 10)
    if n < 10 then d :: acc else natDigitsGo fuel (n / 10) (d :: acc)

def natDigits (n : Nat) : List Char := natDigitsGo (n + 1) n []

def printNat (n : Nat) : String := String.ofList (natDigits n)

def printTy : Ty → String
  | .int => "int "
  | .bool => "bool "

def printUnOp : UnOp → String
  | .neg => "- "
  | .notB => "! "

def printBinOp : BinOp → String
  | .add => "+ "
  | .sub => "- "
  | .mul => "* "
  | .div => "/ "
  | .mod => "% "
  | .lt => "< "
  | .le => "<= "
  | .eqI => "== "
  | .eqB => "== "
  | .andB => "&& "
  | .orB => "|| "

mutual
  def printExpr : Expr → String
    | .intLit n =>
      if n < 0 then "( - " ++ printNat n.natAbs ++ " ) "
      else printNat n.natAbs ++ " "
    | .boolLit true => "true "
    | .boolLit false => "false "
    | .var x => x ++ " "
    | .unop op e => "( " ++ printUnOp op ++ printExpr e ++ ") "
    | .binop op l r => "( " ++ printExpr l ++ printBinOp op ++ printExpr r ++ ") "
    | .ite c t e =>
      "( if " ++ printExpr c ++ "then " ++ printExpr t ++ "else " ++ printExpr e ++ ") "
    | .letE x bound body =>
      "( let " ++ x ++ " = " ++ printExpr bound ++ "in " ++ printExpr body ++ ") "
    | .call f args => f ++ " ( " ++ printArgs args ++ ") "

  def printArgs : Args → String
    | .nil => ""
    | .cons e .nil => printExpr e
    | .cons e rest => printExpr e ++ ", " ++ printArgs rest
end

def printParams : List (String × Ty) → String
  | [] => ""
  | [(x, τ)] => x ++ " : " ++ printTy τ
  | (x, τ) :: rest => x ++ " : " ++ printTy τ ++ ", " ++ printParams rest

def printFun (d : FunDef) : String :=
  "def " ++ d.name ++ " ( " ++ printParams d.params ++ ") : " ++
    printTy d.retTy ++ "= " ++ printExpr d.body

def printFuns : List FunDef → String
  | [] => ""
  | d :: rest => printFun d ++ printFuns rest

def printProgram (p : Program) : String :=
  printFuns p.funs ++ printExpr p.main

end Shallot
