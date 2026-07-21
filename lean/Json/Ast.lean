import Shallot.Peg.Syntax

/-!
# JSON abstract syntax (RFC 8259)

Design principles:

- **Numbers keep their SYNTAX.** RFC 8259 deliberately does not prescribe a
  number representation ("This specification allows implementations to set
  limits on the range and precision"). Collapsing to `Float`/`Int` at parse
  time would bake an implementation choice into the formalization — so
  `JNumber` stores sign / integer digits / fraction digits / exponent
  verbatim, and INTERPRETATION (to rationals etc.) is a separate layer.
  This also makes the roundtrip theorem exact.
- **Strings are DECODED code-point lists.** `\uXXXX` escapes (including
  surrogate pairs) are resolved at parse time; the canonical printer picks
  the escape form on the way out. Our `Char` is a Unicode scalar value.
- **Mutual inductives, no `List JValue`** — the Shallot lesson: nested
  inductives make bare-Lean induction painful; the mutual triple
  `JValue`/`JArray`/`JMembers` gives clean mutual induction and extracts to
  three sealed traits.
- Duplicate object keys are syntactically legal in RFC 8259 ("The names
  within an object SHOULD be unique") — the AST preserves them as-is.
-/

namespace Shallot.Json

/-- Exponent sign as WRITTEN: `e+5`, `e-5` and `e5` are all preserved
distinctly (syntax fidelity ⇒ exact roundtrip). -/
inductive ExpSign where
  | plus
  | minus
  | none

/-- A JSON number, syntax-verbatim.
Well-formedness (`wfNumber`: digits are digits, `intPart` is `0` or starts
non-zero, `fracPart`/exponent digits nonempty when present) lives in
`Json/Wf.lean` — a value violating it is unprintable-as-JSON, not unparseable. -/
structure JNumber where
  neg : Bool
  /-- Integer-part digits, e.g. `['4','2']`. RFC: `0` or non-zero-leading. -/
  intPart : List Char
  /-- Fraction digits; `[]` means "no fraction part". -/
  fracPart : List Char
  /-- Exponent: sign-as-written and digits; `Option.none` = no exponent. -/
  expPart : Option (ExpSign × List Char)

mutual
  inductive JValue where
    | jnull
    | jbool (b : Bool)
    | jnum (n : JNumber)
    /-- Decoded code points (escapes already resolved). -/
    | jstr (s : List Char)
    | jarr (vs : JArray)
    | jobj (ms : JMembers)

  inductive JArray where
    | nil
    | cons (v : JValue) (rest : JArray)

  inductive JMembers where
    | nil
    /-- Key is a decoded string, like `jstr`. Duplicates preserved. -/
    | cons (k : List Char) (v : JValue) (rest : JMembers)
end

def JArray.toList : JArray → List JValue
  | .nil => []
  | .cons v rest => v :: rest.toList

def JMembers.toList : JMembers → List (List Char × JValue)
  | .nil => []
  | .cons k v rest => (k, v) :: rest.toList

end Shallot.Json
