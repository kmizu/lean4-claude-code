/-!
# PEG syntax, parse trees, outcomes

Design decisions (see docs/roadmap.md and the plan):
- deep embedding, Ford-faithful: prioritized choice, primitive `star`,
  not-predicate; `lit` is primitive (one derivation node per keyword)
- input is `List Char`, positions are suffixes — no index arithmetic
- `PTree` mirrors `PExp` structure (NO `List PTree` — avoids nested-inductive
  recursor pain); the outcome carries the tree, so semantics determinism
  gives tree uniqueness for free
- nonterminals are `Nat` indices into `Grammar.rules`; a missing index has an
  explicit failure rule, so NO grammar well-formedness hypotheses anywhere
- extractable subset: monomorphic helpers only (own `stripPrefix?`/`ruleAt`
  instead of polymorphic stdlib functions), comparisons through `Nat`
-/

namespace Shallot

/-- Char equality via codepoints (extraction-friendly, no typeclasses). -/
def beqChar (a b : Char) : Bool := a.toNat == b.toNat

/-- Char ordering via codepoints. -/
def leChar (a b : Char) : Bool := Nat.ble a.toNat b.toNat

/-- `stripPrefix? s input = some rest` iff `input = s ++ rest`. -/
def stripPrefix? : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | c :: cs, d :: ds => if beqChar c d then stripPrefix? cs ds else none

inductive PExp where
  /-- ε — always succeeds, consumes nothing. -/
  | eps
  /-- `.` — any single character. -/
  | any
  /-- A single character literal. -/
  | chr (c : Char)
  /-- Character class `[lo-hi]` (inclusive, by codepoint). -/
  | range (lo hi : Char)
  /-- A literal string (primitive: one node per keyword). -/
  | lit (s : List Char)
  /-- Nonterminal, an index into `Grammar.rules`. -/
  | nt (i : Nat)
  | seq (e₁ e₂ : PExp)
  /-- Prioritized choice `e₁ / e₂`. -/
  | alt (e₁ e₂ : PExp)
  /-- Ford-primitive `e*` (greedy, never fails). -/
  | star (e : PExp)
  /-- Not-predicate `!e` — consumes nothing. -/
  | notP (e : PExp)

/-- And-predicate `&e := !!e`. -/
def PExp.andP (e : PExp) : PExp := .notP (.notP e)

/-- Option `e? := e / ε`. -/
def PExp.opt (e : PExp) : PExp := .alt e .eps

/-- One-or-more `e+ := e e*`. -/
def PExp.plus (e : PExp) : PExp := .seq e (.star e)

/-- Parse trees, mirroring `PExp` structure. -/
inductive PTree where
  /-- Consumed characters of `eps`/`any`/`chr`/`range`/`lit` (ε ⇒ `[]`). -/
  | leaf (cs : List Char)
  | nodeNT (i : Nat) (t : PTree)
  | seq (l r : PTree)
  | choiceL (t : PTree)
  | choiceR (t : PTree)
  | starNil
  /-- `tl` is the tree of the REST of the star. -/
  | starCons (hd tl : PTree)
  /-- Successful not-predicate. -/
  | notT

inductive Outcome where
  | fail
  | ok (t : PTree) (rest : List Char)

structure Grammar where
  rules : List PExp
  start : Nat

/-- Monomorphic list lookup (`Grammar.rules[i]?`). -/
def ruleAt : List PExp → Nat → Option PExp
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, n + 1 => ruleAt rs n

/-- Monomorphic length (stdlib `List.length` is polymorphic). -/
def lenChars : List Char → Nat
  | [] => 0
  | _ :: rest => 1 + lenChars rest

end Shallot
