import Lens.MiniScala
import Lens.Mangle

/-!
# MiniScala → Scala 3 pretty-printer

The single place that owns Scala idiom: literal escaping, keyword quoting,
builtin rendering, layout. v0 keeps expressions on one line and blocks
compact; layout polish comes with bigger extracted bodies (M2+).
-/

namespace Lens.Printer

open Lens.MS

/-! ## Literals -/

def hex4 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  let pad := String.ofList (List.replicate (4 - s.length) '0')
  pad ++ s

/-- Escape one scalar value into Scala string-literal syntax (UTF-16 aware:
astral code points become surrogate pairs). -/
def escapeChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\t' then "\\t"
  else if c == '\r' then "\\r"
  else if 0x20 ≤ c.toNat && c.toNat < 0x7F then String.singleton c
  else if c.toNat ≤ 0xFFFF then "\\u" ++ hex4 c.toNat
  else
    let v := c.toNat - 0x10000
    "\\u" ++ hex4 (0xD800 + v / 0x400) ++ "\\u" ++ hex4 (0xDC00 + v % 0x400)

def escapeString (s : String) : String :=
  s.toList.foldl (init := "") fun acc c => acc ++ escapeChar c

def renderLit : Lit → String
  | .int v =>
    if v < 0 then s!"BigInt({v})"
    else if v ≤ 0x3FFFFFFFFFFFFFFF then s!"BigInt({v})"
    else s!"BigInt(\"{v}\")"
  | .str v => s!"\"{escapeString v}\""
  | .bool true => "true"
  | .bool false => "false"
  | .char cp => s!"0x{String.ofList (Nat.toDigits 16 cp)} /* char */"
  | .unit => "()"

/-! ## Types -/

def renderQualId (q : QualId) : String :=
  String.intercalate "." (q.map Mangle.quoteIfKeyword)

partial def renderType : SType → String
  | .named id [] => renderQualId id
  | .named id args => s!"{renderQualId id}[{String.intercalate ", " (args.map renderType)}]"
  | .tvar n => n
  | .func doms cod => s!"({String.intercalate ", " (doms.map renderType)}) => {renderType cod}"
  | .tuple es => s!"({String.intercalate ", " (es.map renderType)})"
  | .bigint => "BigInt"
  | .string => "String"
  | .char => "Int" -- codepoint representation; a dedicated LChar arrives with the PEG milestone
  | .boolean => "Boolean"
  | .unit => "Unit"
  | .erased => "Unit"

/-! ## Expressions -/

def renderBuiltin (key : String) (args : List String) : String :=
  match key, args with
  | "add", [a, b] => s!"({a} + {b})"
  | "sub", [a, b] => s!"({a} - {b})"
  | "mul", [a, b] => s!"({a} * {b})"
  | "neg", [a] => s!"(-{a})"
  | "natSub", [a, b] => s!"RT.natSub({a}, {b})"
  | "natDiv", [a, b] => s!"RT.natDiv({a}, {b})"
  | "natMod", [a, b] => s!"RT.natMod({a}, {b})"
  | "intDiv", [a, b] => s!"RT.intDiv({a}, {b})"
  | "intMod", [a, b] => s!"RT.intMod({a}, {b})"
  | "strAppend", [a, b] => s!"({a} + {b})"
  | "nil", [] => "Nil"
  | "cons", [h, t] => s!"({h} :: {t})"
  | "none", [] => "None"
  | "some", [a] => s!"Some({a})"
  | "left", [a] => s!"Left({a})"
  | "right", [a] => s!"Right({a})"
  | "tuple2", [a, b] => s!"({a}, {b})"
  | _, _ => s!"__LENS_UNKNOWN_BUILTIN_{key}__" -- deliberately un-compilable

partial def renderPat : Pat → String
  | .ctor id [] => s!"{renderQualId id}()"
  | .ctor id args => s!"{renderQualId id}({String.intercalate ", " (args.map renderPat)})"
  | .var n => Mangle.quoteIfKeyword n
  | .lit l => renderLit l
  | .wild => "_"
  | .tuple args => s!"({String.intercalate ", " (args.map renderPat)})"

partial def renderExpr : SExpr → String
  | .var n => Mangle.quoteIfKeyword n
  | .global id [] => renderQualId id
  | .global id targs => s!"{renderQualId id}[{String.intercalate ", " (targs.map renderType)}]"
  | .lit l => renderLit l
  | .app fn args => s!"{renderExpr fn}({String.intercalate ", " (args.map renderExpr)})"
  | .ctorApp id targs args =>
    let t := if targs.isEmpty then "" else s!"[{String.intercalate ", " (targs.map renderType)}]"
    s!"{renderQualId id}{t}({String.intercalate ", " (args.map renderExpr)})"
  | .lam params body =>
    let ps := params.map fun (n, t) => s!"{Mangle.quoteIfKeyword n}: {renderType t}"
    s!"(({String.intercalate ", " ps}) => {renderExpr body})"
  | .letE n ty v body =>
    let t := match ty with | some t => s!": {renderType t}" | none => ""
    "{ val " ++ Mangle.quoteIfKeyword n ++ t ++ " = " ++ renderExpr v ++ "; " ++ renderExpr body ++ " }"
  | .matchE scrut cases =>
    let cs := cases.map fun (p, b) => s!"case {renderPat p} => {renderExpr b}"
    s!"({renderExpr scrut} match \{ {String.intercalate " ; " cs} })"
  | .ite c t e => s!"(if {renderExpr c} then {renderExpr t} else {renderExpr e})"
  | .proj f target => s!"{renderExpr target}.{Mangle.quoteIfKeyword f}"
  | .ascribe e ty => s!"({renderExpr e}: {renderType ty})"
  | .panic msg => s!"RT.panic(\"{escapeString msg}\")"
  | .builtin key args => renderBuiltin key (args.map renderExpr)

/-! ## Declarations -/

def renderTParams : List String → String
  | [] => ""
  | tps => s!"[{String.intercalate ", " tps}]"

def renderFields (fields : List (String × SType)) : String :=
  String.intercalate ", " (fields.map fun (n, t) => s!"{Mangle.quoteIfKeyword n}: {renderType t}")

def renderDecl : SDecl → String
  | .adt name tparams ctors =>
    let tps := renderTParams tparams
    let parent := if tparams.isEmpty then name else s!"{name}{tps}"
    let cs := ctors.map fun (cn, fields) =>
      s!"  final case class {Mangle.quoteIfKeyword cn}{tps}({renderFields fields}) extends {parent}"
    s!"sealed trait {Mangle.quoteIfKeyword name}{tps}\n" ++
    s!"object {Mangle.quoteIfKeyword name} \{\n" ++ String.intercalate "\n" cs ++ "\n}"
  | .caseClass name tparams fields =>
    s!"final case class {Mangle.quoteIfKeyword name}{renderTParams tparams}({renderFields fields})"
  | .defn name tparams params ret body tailrec =>
    let tr := if tailrec then "@annotation.tailrec\n" else ""
    let ps := if params.isEmpty then "" else s!"({renderFields params})"
    s!"{tr}def {Mangle.quoteIfKeyword name}{renderTParams tparams}{ps}: {renderType ret} =\n  {renderExpr body}"

def renderModule (m : SModule) : String :=
  let header := m.header.map (s!"// {·}")
  String.intercalate "\n" header ++ "\n" ++
  s!"package {m.pkg}\n\n" ++
  "import shallot.rt.Prelude as RT\n\n" ++
  String.intercalate "\n\n" (m.decls.map renderDecl) ++ "\n"

end Lens.Printer
