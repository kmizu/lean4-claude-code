import Json.Ast
import Json.Grammar
import Shallot.Syntax.TreeToAst

/-!
# Parse-tree → JValue extraction

Same discipline as Shallot's `TreeToAst`: recursive extractors destructure
the tree spine with direct nested patterns (structural recursion, no
`partial`), leaf-level helpers do the character work.

String decoding resolves escapes INCLUDING surrogate pairs: escape
sequences produce UTF-16 code units (`Nat`), and `combineUnits` fuses
high/low pairs into scalar values. A **lone surrogate is rejected**
(`loneSurrogate`) — RFC 8259 leaves unpaired surrogates
implementation-defined ("behavior is unpredictable"); rejecting is the
conservative choice and is documented here as ours.
-/

namespace Shallot.Json

inductive JErr where
  | fuelOut
  | syntaxErr
  | shape
  | loneSurrogate

def JErr.render : JErr → String
  | .fuelOut => "FuelOut"
  | .syntaxErr => "SyntaxError"
  | .shape => "ShapeError"
  | .loneSurrogate => "LoneSurrogate"

/-- Hex digit value (grammar guarantees `[0-9a-fA-F]`). -/
def hexVal (c : Char) : Nat :=
  if leChar '0' c && leChar c '9' then c.toNat - '0'.toNat
  else if leChar 'a' c && leChar c 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- One `HEXDIG` node → value. -/
def hexOf : PTree → Except JErr Nat
  | t =>
    match t.chars with
    | [c] => .ok (hexVal c)
    | _ => .error .shape

/-- rule 8 escape → UTF-16 code unit. -/
def escapeOf : PTree → Except JErr Nat
  | .choiceL _ => .ok '"'.toNat
  | .choiceR (.choiceL _) => .ok '\\'.toNat
  | .choiceR (.choiceR (.choiceL _)) => .ok '/'.toNat
  | .choiceR (.choiceR (.choiceR (.choiceL _))) => .ok 0x08
  | .choiceR (.choiceR (.choiceR (.choiceR (.choiceL _)))) => .ok 0x0C
  | .choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceL _))))) => .ok 0x0A
  | .choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceL _)))))) => .ok 0x0D
  | .choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceL _))))))) => .ok 0x09
  | .choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR
      (.seq _ (.seq (.nodeNT _ h1) (.seq (.nodeNT _ h2) (.seq (.nodeNT _ h3) (.nodeNT _ h4)))))))))))) => do
    let a ← hexOf h1
    let b ← hexOf h2
    let c ← hexOf h3
    let d ← hexOf h4
    .ok (((a * 16 + b) * 16 + c) * 16 + d)
  | _ => .error .shape

/-- rule 7 char → UTF-16 code unit (unescaped chars are already scalars). -/
def charUnitOf : PTree → Except JErr Nat
  | .choiceL t =>
    match t.chars with
    | [c] => .ok c.toNat
    | _ => .error .shape
  | .choiceR (.seq _ (.nodeNT _ escT)) => escapeOf escT
  | _ => .error .shape

def charUnits : PTree → Except JErr (List Nat)
  | .starCons (.nodeNT _ cT) rest => do
    .ok ((← charUnitOf cT) :: (← charUnits rest))
  | .starNil => .ok []
  | _ => .error .shape

/-- Fuse UTF-16 units into scalar values; lone surrogates are rejected. -/
def combineUnits : List Nat → Except JErr (List Char)
  | [] => .ok []
  | u :: rest =>
    if 0xD800 ≤ u && u ≤ 0xDBFF then
      match rest with
      | lo :: rest' =>
        if 0xDC00 ≤ lo && lo ≤ 0xDFFF then
          match combineUnits rest' with
          | .ok cs => .ok (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (lo - 0xDC00)) :: cs)
          | .error e => .error e
        else .error .loneSurrogate
      | [] => .error .loneSurrogate
    else if 0xDC00 ≤ u && u ≤ 0xDFFF then .error .loneSurrogate
    else
      match combineUnits rest with
      | .ok cs => .ok (Char.ofNat u :: cs)
      | .error e => .error e

/-- rule 6 string → decoded code points. -/
def stringOf : PTree → Except JErr (List Char)
  | .seq _ (.seq starT _) => do
    combineUnits (← charUnits starT)
  | _ => .error .shape

/-- rule 10 int: both alternatives' digit span IS the consumed chars. -/
def intOf (t : PTree) : List Char := t.chars

/-- rule 11 frac: drop the leading `'.'`. -/
def fracOf : PTree → Except JErr (List Char)
  | .seq _ digitsT => .ok digitsT.chars
  | _ => .error .shape

/-- rule 12 exp: `('e'/'E') ('-'/'+')? digits`, everything as written.
Note the sign is `opt (alt - +)`, so its tree nests TWO choices. -/
def expOf : PTree → Except JErr JExp
  | .seq eT (.seq signOptT digitsT) => do
    let upper ← match eT with
      | .choiceL _ => pure false
      | .choiceR _ => pure true
      | _ => .error .shape
    let sign ← match signOptT with
      | .choiceR _ => pure ExpSign.none
      | .choiceL (.choiceL _) => pure ExpSign.minus
      | .choiceL (.choiceR _) => pure ExpSign.plus
      | _ => .error .shape
    .ok { upper, sign, digits := digitsT.chars }
  | _ => .error .shape

/-- rule 9 number. -/
def numberOf : PTree → Except JErr JNumber
  | .seq minusOptT (.seq (.nodeNT _ intT) (.seq fracOptT expOptT)) => do
    let neg ← match minusOptT with
      | .choiceR _ => pure false
      | .choiceL _ => pure true
      | _ => .error .shape
    let fracPart ← match fracOptT with
      | .choiceR _ => pure ([] : List Char)
      | .choiceL (.nodeNT _ fT) => fracOf fT
      | _ => .error .shape
    let expPart ← match expOptT with
      | .choiceR _ => pure (Option.none : Option JExp)
      | .choiceL (.nodeNT _ eT) => do
        pure (Option.some (← expOf eT))
      | _ => .error .shape
    .ok { neg, intPart := intOf intT, fracPart, expPart }
  | _ => .error .shape

mutual
  /-- rule 2 value (RFC alternative order). -/
  def valueOf : PTree → Except JErr JValue
    | .choiceL _ => .ok (.jbool false)
    | .choiceR (.choiceL _) => .ok .jnull
    | .choiceR (.choiceR (.choiceL _)) => .ok (.jbool true)
    | .choiceR (.choiceR (.choiceR (.choiceL (.nodeNT _ oT)))) => objectOf oT
    | .choiceR (.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT _ aT))))) => arrayOf aT
    | .choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceL (.nodeNT _ nT)))))) => do
      .ok (.jnum (← numberOf nT))
    | .choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.choiceR (.nodeNT _ sT)))))) => do
      .ok (.jstr (← stringOf sT))
    | _ => .error .shape

  /-- rule 3 object. -/
  def objectOf : PTree → Except JErr JValue
    | .seq _ (.seq membersOptT _) =>
      match membersOptT with
      | .choiceR _ => .ok (.jobj .nil)
      | .choiceL (.seq (.nodeNT _ m0T) starT) => do
        let (k, v) ← memberKeyOf m0T
        .ok (.jobj (.cons k v (← memberItems starT)))
      | _ => .error .shape
    | _ => .error .shape

  /-- rule 4 member (key, value). -/
  def memberKeyOf : PTree → Except JErr (List Char × JValue)
    | .seq (.nodeNT _ sT) (.seq _ (.nodeNT _ vT)) => do
      .ok (← stringOf sT, ← valueOf vT)
    | _ => .error .shape

  def memberItems : PTree → Except JErr JMembers
    | .starCons (.seq _ (.nodeNT _ mT)) rest => do
      let (k, v) ← memberKeyOf mT
      .ok (.cons k v (← memberItems rest))
    | .starNil => .ok .nil
    | _ => .error .shape

  /-- rule 5 array. -/
  def arrayOf : PTree → Except JErr JValue
    | .seq _ (.seq valuesOptT _) =>
      match valuesOptT with
      | .choiceR _ => .ok (.jarr .nil)
      | .choiceL (.seq (.nodeNT _ v0T) starT) => do
        .ok (.jarr (.cons (← valueOf v0T) (← arrayItems starT)))
      | _ => .error .shape
    | _ => .error .shape

  def arrayItems : PTree → Except JErr JArray
    | .starCons (.seq _ (.nodeNT _ vT)) rest => do
      .ok (.cons (← valueOf vT) (← arrayItems rest))
    | .starNil => .ok .nil
    | _ => .error .shape
end

/-- The JSON parser: the VERIFIED generic PEG interpreter applied to
`jsonGrammar`, then tree extraction. -/
def parseJson (fuel : Nat) (s : String) : Except JErr JValue :=
  match pegRun jsonGrammar fuel (.nt JNT.jsonText) s.toList with
  | none => .error .fuelOut
  | some .fail => .error .syntaxErr
  | some (.ok (.nodeNT _ (.seq _ (.seq (.nodeNT _ vT) _))) _) => valueOf vT
  | some (.ok _ _) => .error .shape

end Shallot.Json
