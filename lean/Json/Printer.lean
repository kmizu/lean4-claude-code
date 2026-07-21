import Json.Ast

/-!
# Canonical JSON printer

Machine-oriented canonical form: no whitespace, `"` and `\` escaped with
their short forms, control characters (< 0x20) as lowercase `\uXXXX`,
everything else emitted as raw code points (our strings are already
decoded scalars, so astral characters need no surrogate escapes on the
way OUT — RFC 8259 permits raw non-ASCII). Numbers reproduce their stored
syntax verbatim, which is what makes the roundtrip theorem exact.
-/

namespace Shallot.Json

def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Four lowercase hex digits (code units are ≤ 0xFFFF here). -/
def hex4 (n : Nat) : List Char :=
  [hexDigitChar (n / 4096 % 16), hexDigitChar (n / 256 % 16),
   hexDigitChar (n / 16 % 16), hexDigitChar (n % 16)]

/-- Canonical escape of one decoded code point. -/
def escapeCp (c : Char) : List Char :=
  if beqChar c '"' then ['\\', '"']
  else if beqChar c '\\' then ['\\', '\\']
  else if Nat.blt c.toNat 0x20 then '\\' :: 'u' :: hex4 c.toNat
  else [c]

def escChars : List Char → List Char
  | [] => []
  | c :: rest => escapeCp c ++ escChars rest

def printString (s : List Char) : List Char :=
  '"' :: escChars s ++ ['"']

def printExp : Option JExp → List Char
  | Option.none => []
  | Option.some e =>
    let signChars := match e.sign with
      | .plus => ['+']
      | .minus => ['-']
      | .none => []
    (if e.upper then 'E' else 'e') :: signChars ++ e.digits

def printNumber (n : JNumber) : List Char :=
  (if n.neg then ['-'] else []) ++ n.intPart ++
  (match n.fracPart with
   | [] => []
   | ds => '.' :: ds) ++
  printExp n.expPart

mutual
  def printValue : JValue → List Char
    | .jnull => "null".toList
    | .jbool true => "true".toList
    | .jbool false => "false".toList
    | .jnum n => printNumber n
    | .jstr s => printString s
    | .jarr vs => '[' :: printItems vs ++ [']']
    | .jobj ms => '{' :: printMembers ms ++ ['}']

  def printItems : JArray → List Char
    | .nil => []
    | .cons v .nil => printValue v
    | .cons v rest => printValue v ++ ',' :: printItems rest

  def printMembers : JMembers → List Char
    | .nil => []
    | .cons k v .nil => printString k ++ ':' :: printValue v
    | .cons k v rest => printString k ++ ':' :: printValue v ++ ',' :: printMembers rest
end

def printJson (v : JValue) : String :=
  String.ofList (printValue v)

end Shallot.Json
