import Lean

/-!
# Name mangling: Lean names → valid Scala identifiers

Rules (fixed here, applied by the printer via `quoteIfKeyword`):
- strip the configured prefix (`Shallot.`), join remaining segments with `_`
- `'` → `_p`; ASCII `[A-Za-z0-9_]` pass through; anything else → `_uXXXX`
- Scala keywords are backtick-quoted at print time (never renamed)
- collisions with Scala/Java built-in type names get a `Lean_` prefix
-/

namespace Lens.Mangle

open Lean

def scalaKeywords : List String :=
  ["abstract", "case", "catch", "class", "def", "do", "else", "enum", "export",
   "extends", "false", "final", "finally", "for", "given", "if", "implicit",
   "import", "lazy", "match", "new", "null", "object", "override", "package",
   "private", "protected", "return", "sealed", "super", "then", "throw",
   "trait", "true", "try", "type", "val", "var", "while", "with", "yield"]

/-- Names that would shadow ubiquitous Scala/Java types if emitted bare. -/
def denyList : List String :=
  ["List", "Option", "Some", "None", "Nil", "Either", "Left", "Right",
   "String", "Char", "Boolean", "Unit", "Int", "Long", "BigInt", "Map",
   "Seq", "Vector", "Array", "Set", "Predef", "Nothing", "Any", "AnyRef"]

def sanitizeChar (c : Char) : String :=
  if c.isAlphanum || c == '_' then String.singleton c
  else if c == '\'' then "_p"
  else "_u" ++ String.ofList (Nat.toDigits 16 c.toNat)

def sanitizeSegment (s : String) : String :=
  let out := s.toList.foldl (init := "") fun acc c => acc ++ sanitizeChar c
  if out.isEmpty then "_x"
  else if out.front.isDigit then "_" ++ out
  else out

/-- Mangle a full Lean name into one flat Scala identifier. -/
def mangle (stripPfx : Name) (n : Name) : String :=
  let n := if stripPfx.isPrefixOf n then n.replacePrefix stripPfx .anonymous else n
  let segs := n.components.map fun c => sanitizeSegment c.toString
  let out := String.intercalate "_" segs
  if denyList.contains out then "Lean_" ++ out else out

/-- Last segment only (for constructor names inside a companion object). -/
def mangleLast (n : Name) : String :=
  match n with
  | .str _ s => sanitizeSegment s
  | _ => sanitizeSegment n.toString

/-- Printer-side: backtick-quote Scala keywords. -/
def quoteIfKeyword (s : String) : String :=
  if scalaKeywords.contains s then s!"`{s}`" else s

/-- Local binder name: sanitize, replacing macro-scoped/anonymous names. -/
def binderName (n : Name) (fresh : Nat) : String :=
  if n.hasMacroScopes || n == .anonymous then s!"x{fresh}"
  else sanitizeSegment n.toString

end Lens.Mangle
