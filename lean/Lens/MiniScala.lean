/-!
# MiniScala IR

The small ML-like intermediate representation between Lean declarations and
Scala 3 source (the Coq-extraction / Letouzey architecture). Every translation
route (equations, raw terms, LCNF) targets this IR; a single pretty-printer
(`Lens.Printer`) owns all Scala idiom — name quoting, literal escaping,
builtin rendering, layout.
-/

namespace Lens.MS

/-- Already-mangled name segments, e.g. `["Color", "red"]` → `Color.red`. -/
abbrev QualId := List String

inductive SType where
  | named (id : QualId) (args : List SType)
  | tvar (name : String)
  | func (dom : List SType) (cod : SType)
  | tuple (elems : List SType)
  | bigint | string | char | boolean | unit
  | erased
  deriving Inhabited, Repr, BEq

inductive Lit where
  | int (v : Int)
  | str (v : String)
  | bool (v : Bool)
  | char (codepoint : Nat)
  | unit
  deriving Inhabited, Repr, BEq

inductive Pat where
  | ctor (id : QualId) (args : List Pat)
  | var (name : String)
  | lit (l : Lit)
  | wild
  | tuple (args : List Pat)
  deriving Inhabited, Repr

inductive SExpr where
  | var (name : String)
  | global (id : QualId) (targs : List SType)
  | lit (l : Lit)
  | app (fn : SExpr) (args : List SExpr)
  /-- Constructor application; explicit type args because extracted ADTs are
  invariant and Scala's inference needs the help. -/
  | ctorApp (id : QualId) (targs : List SType) (args : List SExpr)
  | lam (params : List (String × SType)) (body : SExpr)
  | letE (name : String) (ty : Option SType) (value : SExpr) (body : SExpr)
  | matchE (scrut : SExpr) (cases : List (Pat × SExpr))
  | ite (c t e : SExpr)
  | proj (field : String) (target : SExpr)
  | ascribe (e : SExpr) (ty : SType)
  | panic (msg : String)
  /-- Printer-resolved primitive, e.g. `add`, `natSub`, `strAppend`. -/
  | builtin (key : String) (args : List SExpr)
  deriving Inhabited, Repr

inductive SDecl where
  /-- `sealed trait N[tp]` + companion `final case class c(fields) extends N`. -/
  | adt (name : String) (tparams : List String)
        (ctors : List (String × List (String × SType)))
  /-- Lean structure → plain `final case class`. -/
  | caseClass (name : String) (tparams : List String) (fields : List (String × SType))
  | defn (name : String) (tparams : List String) (params : List (String × SType))
         (ret : SType) (body : SExpr) (tailrec : Bool)
  deriving Inhabited, Repr

structure SModule where
  pkg : String
  header : List String
  decls : List SDecl
  deriving Inhabited

/-- Names an `SDecl` introduces (for ordering/grouping). -/
def SDecl.name : SDecl → String
  | .adt n .. => n
  | .caseClass n .. => n
  | .defn n .. => n

def SDecl.isType : SDecl → Bool
  | .adt .. | .caseClass .. => true
  | .defn .. => false

end Lens.MS
