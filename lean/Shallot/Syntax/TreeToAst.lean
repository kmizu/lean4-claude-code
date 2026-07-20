import Shallot.Syntax.Grammar
import Shallot.Peg.Interp
import Shallot.Lang.Ast

/-!
# Parse-tree → AST extraction

Walks the `PTree` produced by `pegRun` on `shallotGrammar`. Recursive
extractors destructure the tree spine with DIRECT nested patterns so the
recursion is visibly structural (no `partial` — extractable subset, and the
equations feed the roundtrip proofs). Leaf-level extraction (identifier
spans, digits) uses ordinary helpers.

`unop neg (intLit k)` normalizes to `intLit (-k)` (printer-normal form).
Node indices inside `nodeNT` are NOT re-checked: for trees produced by the
grammar the positions determine them, and the roundtrip theorem only ever
speaks about such trees.
-/

namespace Shallot

inductive ParseErr where
  | fuelOut
  | syntaxErr
  | shape

def ParseErr.render : ParseErr → String
  | .fuelOut => "FuelOut"
  | .syntaxErr => "SyntaxError"
  | .shape => "ShapeError"

/-- All characters consumed by a subtree, in order. -/
def PTree.chars : PTree → List Char
  | .leaf cs => cs
  | .nodeNT _ t => t.chars
  | .seq l r => l.chars ++ r.chars
  | .choiceL t => t.chars
  | .choiceR t => t.chars
  | .starNil => []
  | .starCons h t => h.chars ++ t.chars
  | .notT => []

def digitsValGo : List Char → Nat → Nat
  | [], acc => acc
  | c :: rest, acc => digitsValGo rest (acc * 10 + (c.toNat - '0'.toNat))

/-- Value of a digit span. -/
def digitsVal (cs : List Char) : Nat := digitsValGo cs 0

/-- Ident rule: `seq (notP …) (seq (seq idStart (star idCont)) Spacing)` —
the name is the character span of the core. -/
def identName : PTree → Except ParseErr String
  | .seq _ (.seq core _) => .ok (String.ofList core.chars)
  | _ => .error .shape

/-- Number rule: `seq (seq digit (star digit)) Spacing`. -/
def numberVal : PTree → Except ParseErr Int
  | .seq core _ => .ok (Int.ofNat (digitsVal core.chars))
  | _ => .error .shape

/-- Type rule: `alt (kw "int") (kw "bool")`. -/
def typeOf : PTree → Except ParseErr Ty
  | .choiceL _ => .ok .int
  | .choiceR _ => .ok .bool
  | _ => .error .shape

mutual
  /-- NT.expr: `alt IfExpr (alt LetExpr OrE)`. -/
  def exprOf : PTree → Except ParseErr Expr
    | .choiceL (.nodeNT _ t) => ifOf t
    | .choiceR (.choiceL (.nodeNT _ t)) => letOf t
    | .choiceR (.choiceR (.nodeNT _ t)) => orOf t
    | _ => .error .shape

  /-- NT.ifExpr: `kwIf Expr kwThen Expr kwElse Expr`. -/
  def ifOf : PTree → Except ParseErr Expr
    | .seq _ (.seq (.nodeNT _ cT) (.seq _ (.seq (.nodeNT _ tT) (.seq _ (.nodeNT _ eT))))) => do
      .ok (.ite (← exprOf cT) (← exprOf tT) (← exprOf eT))
    | _ => .error .shape

  /-- NT.letExpr: `kwLet Ident eq Expr kwIn Expr`. -/
  def letOf : PTree → Except ParseErr Expr
    | .seq _ (.seq identT (.seq _ (.seq (.nodeNT _ bT) (.seq _ (.nodeNT _ bodyT))))) => do
      let x ← match identT with
        | .nodeNT _ it => identName it
        | _ => .error .shape
      .ok (.letE x (← exprOf bT) (← exprOf bodyT))
    | _ => .error .shape

  /-- NT.orE: `AndE ("||" AndE)*`. -/
  def orOf : PTree → Except ParseErr Expr
    | .seq (.nodeNT _ hdT) starT => do
      goOr (← andOf hdT) starT
    | _ => .error .shape

  def goOr (acc : Expr) : PTree → Except ParseErr Expr
    | .starCons (.seq _ (.nodeNT _ subT)) rest => do
      goOr (.binop .orB acc (← andOf subT)) rest
    | .starNil => .ok acc
    | _ => .error .shape

  /-- NT.andE: `CmpE ("&&" CmpE)*`. -/
  def andOf : PTree → Except ParseErr Expr
    | .seq (.nodeNT _ hdT) starT => do
      goAnd (← cmpOf hdT) starT
    | _ => .error .shape

  def goAnd (acc : Expr) : PTree → Except ParseErr Expr
    | .starCons (.seq _ (.nodeNT _ subT)) rest => do
      goAnd (.binop .andB acc (← cmpOf subT)) rest
    | .starNil => .ok acc
    | _ => .error .shape

  /-- NT.cmpE: `AddE (("<=" / "<" / "==") AddE)?`. -/
  def cmpOf : PTree → Except ParseErr Expr
    | .seq (.nodeNT _ lT) (.choiceR _) => addOf lT
    | .seq (.nodeNT _ lT) (.choiceL (.seq opT (.nodeNT _ rT))) => do
      let op ← match opT with
        | .choiceL _ => pure BinOp.le
        | .choiceR (.choiceL _) => pure BinOp.lt
        | .choiceR (.choiceR _) => pure BinOp.eqI
        | _ => .error .shape
      .ok (.binop op (← addOf lT) (← addOf rT))
    | _ => .error .shape

  /-- NT.addE: `MulE (("+" / "-") MulE)*`. -/
  def addOf : PTree → Except ParseErr Expr
    | .seq (.nodeNT _ hdT) starT => do
      goAdd (← mulOf hdT) starT
    | _ => .error .shape

  def goAdd (acc : Expr) : PTree → Except ParseErr Expr
    | .starCons (.seq opT (.nodeNT _ subT)) rest => do
      let op ← match opT with
        | .choiceL _ => pure BinOp.add
        | .choiceR _ => pure BinOp.sub
        | _ => .error .shape
      goAdd (.binop op acc (← mulOf subT)) rest
    | .starNil => .ok acc
    | _ => .error .shape

  /-- NT.mulE: `Unary (("*" / "/" / "%") Unary)*`. -/
  def mulOf : PTree → Except ParseErr Expr
    | .seq (.nodeNT _ hdT) starT => do
      goMul (← unaryOf hdT) starT
    | _ => .error .shape

  def goMul (acc : Expr) : PTree → Except ParseErr Expr
    | .starCons (.seq opT (.nodeNT _ subT)) rest => do
      let op ← match opT with
        | .choiceL _ => pure BinOp.mul
        | .choiceR (.choiceL _) => pure BinOp.div
        | .choiceR (.choiceR _) => pure BinOp.mod
        | _ => .error .shape
      goMul (.binop op acc (← unaryOf subT)) rest
    | .starNil => .ok acc
    | _ => .error .shape

  /-- NT.unary: `"-" Unary / "!" Unary / Primary` (with neg-literal
  normalization). -/
  def unaryOf : PTree → Except ParseErr Expr
    | .choiceL (.seq _ (.nodeNT _ subT)) => do
      match ← unaryOf subT with
      | .intLit n => .ok (.intLit (-n))
      | e => .ok (.unop .neg e)
    | .choiceR (.choiceL (.seq _ (.nodeNT _ subT))) => do
      .ok (.unop .notB (← unaryOf subT))
    | .choiceR (.choiceR (.nodeNT _ pT)) => primaryOf pT
    | _ => .error .shape

  /-- NT.primary: `Number / true / false / Call / Ident / "(" Expr ")"`. -/
  def primaryOf : PTree → Except ParseErr Expr
    | .choiceL (.nodeNT _ nT) => do
      .ok (.intLit (← numberVal nT))
    | .choiceR (.choiceL _) => .ok (.boolLit true)
    | .choiceR (.choiceR (.choiceL _)) => .ok (.boolLit false)
    | .choiceR (.choiceR (.choiceR (.choiceL (.nodeNT _ cT)))) => callOf cT
    | .choiceR (.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT _ iT))))) => do
      .ok (.var (← identName iT))
    | .choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.seq _ (.seq (.nodeNT _ eT) _)))))) =>
      exprOf eT
    | _ => .error .shape

  /-- NT.call: `Ident "(" ArgList? ")"`. -/
  def callOf : PTree → Except ParseErr Expr
    | .seq identT (.seq _ (.seq argsOptT _)) => do
      let f ← match identT with
        | .nodeNT _ it => identName it
        | _ => .error .shape
      match argsOptT with
      | .choiceR _ => .ok (.call f .nil)
      | .choiceL (.nodeNT _ alT) => do
        .ok (.call f (← argListOf alT))
      | _ => .error .shape
    | _ => .error .shape

  /-- NT.argList: `Expr ("," Expr)*`. -/
  def argListOf : PTree → Except ParseErr Args
    | .seq (.nodeNT _ hdT) starT => do
      .ok (.cons (← exprOf hdT) (← argItems starT))
    | _ => .error .shape

  def argItems : PTree → Except ParseErr Args
    | .starCons (.seq _ (.nodeNT _ eT)) rest => do
      .ok (.cons (← exprOf eT) (← argItems rest))
    | .starNil => .ok .nil
    | _ => .error .shape
end

/-- NT.param: `Ident ":" Type`. -/
def paramOf : PTree → Except ParseErr (String × Ty)
  | .seq (.nodeNT _ iT) (.seq _ (.nodeNT _ tyT)) => do
    .ok (← identName iT, ← typeOf tyT)
  | _ => .error .shape

def paramItems : PTree → Except ParseErr (List (String × Ty))
  | .starCons (.seq _ (.nodeNT _ pT)) rest => do
    .ok ((← paramOf pT) :: (← paramItems rest))
  | .starNil => .ok []
  | _ => .error .shape

/-- NT.params: `Param ("," Param)*`. -/
def paramsOf : PTree → Except ParseErr (List (String × Ty))
  | .seq (.nodeNT _ hdT) starT => do
    .ok ((← paramOf hdT) :: (← paramItems starT))
  | _ => .error .shape

/-- NT.funDef: `kwDef Ident "(" Params? ")" ":" Type "=" Expr`. -/
def funDefOf : PTree → Except ParseErr FunDef
  | .seq _ (.seq identT (.seq _ (.seq paramsOptT (.seq _ (.seq _ (.seq (.nodeNT _ tyT) (.seq _ (.nodeNT _ bodyT)))))))) => do
    let name ← match identT with
      | .nodeNT _ it => identName it
      | _ => .error .shape
    let params ← match paramsOptT with
      | .choiceR _ => pure []
      | .choiceL (.nodeNT _ pT) => paramsOf pT
      | _ => .error .shape
    .ok { name, params, retTy := ← typeOf tyT, body := ← exprOf bodyT }
  | _ => .error .shape

def funItems : PTree → Except ParseErr (List FunDef)
  | .starCons (.nodeNT _ dT) rest => do
    .ok ((← funDefOf dT) :: (← funItems rest))
  | .starNil => .ok []
  | _ => .error .shape

/-- NT.program: `Spacing FunDef* Expr EOF`. -/
def treeToAst : PTree → Except ParseErr Program
  | .seq _ (.seq starT (.seq (.nodeNT _ eT) _)) => do
    .ok { funs := ← funItems starT, main := ← exprOf eT }
  | _ => .error .shape

/-- The Shallot parser: the VERIFIED generic PEG interpreter applied to
`shallotGrammar`, then tree extraction. -/
def parseShallot (fuel : Nat) (s : String) : Except ParseErr Program :=
  match pegRun shallotGrammar fuel (.nt NT.program) s.toList with
  | none => .error .fuelOut
  | some .fail => .error .syntaxErr
  | some (.ok (.nodeNT _ t) _) => treeToAst t -- unwrap the start-symbol node
  | some (.ok _ _) => .error .shape

end Shallot
