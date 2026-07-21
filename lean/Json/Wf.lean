import Json.Ast

/-!
# JSON well-formedness (milestone J3)

Bool predicates carving out the printable-as-JSON fragment of the AST.
`JNumber` stores its syntax verbatim, so a value like `intPart = ['x']`
is representable but unprintable — `wfNumber` excludes it. The digit
checks use `leChar`, matching the grammar's `range '0' '9'` semantics
exactly (so the J3 lexeme lemmas bridge to `Derives.rangeOk` with no
translation).

Strings need NO condition: they are already scalar code points by type
(`Char` carries a validity proof), and the canonical printer can encode
any of them.
-/

set_option autoImplicit false

namespace Shallot.Json

/-- `1*DIGIT`: nonempty and every char in `'0'..'9'`
(the grammar's `range '0' '9'`, via `leChar`). -/
def wfDigits (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all (fun c => leChar '0' c && leChar c '9')

/-- RFC `int = zero / ( digit1-9 *DIGIT )`: exactly `['0']`, or a head in
`'1'..'9'` followed by digits. -/
def wfInt : List Char → Bool
  | [] => false
  | c :: rest =>
    (beqChar c '0' && rest.isEmpty) ||
    (leChar '1' c && leChar c '9' &&
      rest.all (fun d => leChar '0' d && leChar d '9'))

/-- Exponent digits are `1*DIGIT` (sign and case are unconstrained). -/
def wfExp (e : JExp) : Bool := wfDigits e.digits

/-- A printable number: well-formed `int`, fraction empty-or-`1*DIGIT`,
exponent absent-or-well-formed. -/
def wfNumber (n : JNumber) : Bool :=
  wfInt n.intPart &&
  (n.fracPart.isEmpty || wfDigits n.fracPart) &&
  (match n.expPart with
   | none => true
   | some e => wfExp e)

mutual
  /-- Every embedded `JNumber` satisfies `wfNumber`; strings are
  unconditionally fine (already decoded scalars). -/
  def wfValue : JValue → Bool
    | .jnull => true
    | .jbool _ => true
    | .jnum n => wfNumber n
    | .jstr _ => true
    | .jarr vs => wfArray vs
    | .jobj ms => wfMembers ms

  def wfArray : JArray → Bool
    | .nil => true
    | .cons v rest => wfValue v && wfArray rest

  def wfMembers : JMembers → Bool
    | .nil => true
    | .cons _ v rest => wfValue v && wfMembers rest
end

end Shallot.Json
