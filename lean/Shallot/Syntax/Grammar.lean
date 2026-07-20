import Shallot.Peg.Syntax

/-!
# Shallot concrete syntax, as a PEG

The grammar is DATA (`shallotGrammar : Grammar`); parsing is the verified
generic interpreter `pegRun` — so soundness/determinism/completeness
(T1–T3) apply to the Shallot parser for free.

Scannerless: every token consumes its trailing `Spacing`. PEG showcase
pieces: keyword guards (`"if" !IdCont`), `'=' !'='` disambiguation
(vs `==`), prioritized choice (`Call / Ident`, `"<=" / "<"`), `!.` EOF.

```
Program  <- Spacing FunDef* Expr EOF
FunDef   <- "def" Ident "(" Params? ")" ":" Type "=" Expr
Params   <- Param ("," Param)*        Param <- Ident ":" Type
Type     <- "int" / "bool"
Expr     <- IfExpr / LetExpr / OrE
IfExpr   <- "if" Expr "then" Expr "else" Expr
LetExpr  <- "let" Ident "=" Expr "in" Expr
OrE      <- AndE ("||" AndE)*         AndE <- CmpE ("&&" CmpE)*
CmpE     <- AddE (("<=" / "<" / "==") AddE)?
AddE     <- MulE (("+" / "-") MulE)*  MulE <- Unary (("*" / "/" / "%") Unary)*
Unary    <- "-" Unary / "!" Unary / Primary
Primary  <- Number / "true" / "false" / Call / Ident / "(" Expr ")"
Call     <- Ident "(" ArgList? ")"    ArgList <- Expr ("," Expr)*
```
-/

namespace Shallot

namespace NT

def spacing : Nat := 0
def ident : Nat := 1
def number : Nat := 2
def type' : Nat := 3
def program : Nat := 4
def funDef : Nat := 5
def params : Nat := 6
def param : Nat := 7
def expr : Nat := 8
def ifExpr : Nat := 9
def letExpr : Nat := 10
def orE : Nat := 11
def andE : Nat := 12
def cmpE : Nat := 13
def addE : Nat := 14
def mulE : Nat := 15
def unary : Nat := 16
def primary : Nat := 17
def call : Nat := 18
def argList : Nat := 19

end NT

/-- `idStart <- [a-z] / [A-Z] / '_'` -/
def idStartP : PExp := .alt (.range 'a' 'z') (.alt (.range 'A' 'Z') (.chr '_'))

/-- `idCont <- idStart / [0-9]` -/
def idContP : PExp := .alt idStartP (.range '0' '9')

/-- Keyword: literal + not-followed-by-identifier-char + spacing. -/
def kw (s : String) : PExp :=
  .seq (.lit s.toList) (.seq (.notP idContP) (.nt NT.spacing))

/-- Any reserved word (the `!Keyword` guard inside `Ident`). -/
def keywordP : PExp :=
  .alt (.lit "if".toList) (.alt (.lit "then".toList) (.alt (.lit "else".toList)
    (.alt (.lit "let".toList) (.alt (.lit "in".toList) (.alt (.lit "def".toList)
      (.alt (.lit "true".toList) (.alt (.lit "false".toList)
        (.alt (.lit "int".toList) (.lit "bool".toList)))))))))

/-- Symbol token: literal + spacing. -/
def tok (s : String) : PExp := .seq (.lit s.toList) (.nt NT.spacing)

/-- `'=' !'='` then spacing (assignment, not equality). -/
def eqTok : PExp := .seq (.chr '=') (.seq (.notP (.chr '=')) (.nt NT.spacing))

/-- `'<' !'='` then spacing (less-than, not less-equal). -/
def ltTok : PExp := .seq (.chr '<') (.seq (.notP (.chr '=')) (.nt NT.spacing))

/-- Left-associative operator tier: `Sub (op Sub)*`. -/
def tier (sub : Nat) (ops : PExp) : PExp :=
  .seq (.nt sub) (.star (.seq ops (.nt sub)))

def shallotRules : List PExp :=
  [ -- 0 Spacing
    .star (.alt (.chr ' ') (.alt (.chr '\n') (.alt (.chr '\t') (.chr '\r')))),
    -- 1 Ident: !Keyword-followed-by-non-idCont, then idStart idCont*, spacing
    .seq (.notP (.seq keywordP (.notP idContP)))
      (.seq (.seq idStartP (.star idContP)) (.nt NT.spacing)),
    -- 2 Number
    .seq (.seq (.range '0' '9') (.star (.range '0' '9'))) (.nt NT.spacing),
    -- 3 Type
    .alt (kw "int") (kw "bool"),
    -- 4 Program
    .seq (.nt NT.spacing)
      (.seq (.star (.nt NT.funDef)) (.seq (.nt NT.expr) (.notP .any))),
    -- 5 FunDef
    .seq (kw "def") (.seq (.nt NT.ident)
      (.seq (tok "(") (.seq (PExp.opt (.nt NT.params))
        (.seq (tok ")") (.seq (tok ":") (.seq (.nt NT.type')
          (.seq eqTok (.nt NT.expr)))))))),
    -- 6 Params
    .seq (.nt NT.param) (.star (.seq (tok ",") (.nt NT.param))),
    -- 7 Param
    .seq (.nt NT.ident) (.seq (tok ":") (.nt NT.type')),
    -- 8 Expr
    .alt (.nt NT.ifExpr) (.alt (.nt NT.letExpr) (.nt NT.orE)),
    -- 9 IfExpr
    .seq (kw "if") (.seq (.nt NT.expr)
      (.seq (kw "then") (.seq (.nt NT.expr) (.seq (kw "else") (.nt NT.expr))))),
    -- 10 LetExpr
    .seq (kw "let") (.seq (.nt NT.ident) (.seq eqTok
      (.seq (.nt NT.expr) (.seq (kw "in") (.nt NT.expr))))),
    -- 11 OrE
    tier NT.andE (tok "||"),
    -- 12 AndE
    tier NT.cmpE (tok "&&"),
    -- 13 CmpE: AddE (("<=" / "<" / "==") AddE)?
    .seq (.nt NT.addE)
      (PExp.opt (.seq (.alt (tok "<=") (.alt ltTok (tok "=="))) (.nt NT.addE))),
    -- 14 AddE
    tier NT.mulE (.alt (tok "+") (tok "-")),
    -- 15 MulE
    tier NT.unary (.alt (tok "*") (.alt (tok "/") (tok "%"))),
    -- 16 Unary
    .alt (.seq (tok "-") (.nt NT.unary))
      (.alt (.seq (tok "!") (.nt NT.unary)) (.nt NT.primary)),
    -- 17 Primary
    .alt (.nt NT.number) (.alt (kw "true") (.alt (kw "false")
      (.alt (.nt NT.call) (.alt (.nt NT.ident)
        (.seq (tok "(") (.seq (.nt NT.expr) (tok ")"))))))),
    -- 18 Call
    .seq (.nt NT.ident) (.seq (tok "(") (.seq (PExp.opt (.nt NT.argList)) (tok ")"))),
    -- 19 ArgList
    .seq (.nt NT.expr) (.star (.seq (tok ",") (.nt NT.expr))) ]

def shallotGrammar : Grammar :=
  { rules := shallotRules, start := NT.program }

end Shallot
