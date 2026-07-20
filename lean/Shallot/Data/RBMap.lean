/-!
# Red-black tree map (String keys, type-polymorphic values)

Okasaki-style insertion with the classic four balance cases. Monomorphic
keys via a hand-written `cmpStr` (no typeclasses — extractable subset);
value polymorphism is TYPE polymorphism only, which extracts to a Scala
generic. Invariants and theorems live in `Data/RBVerify.lean` (M6):
`Ordered`, RB balance via the "infrared" insertion invariant, find/insert
model refinement, and the load-bearing `fromList ↔ assocLookup` (R6) used
by the interpreter's function table.

`erase` is deliberately absent for now: verified erase (with rebalancing)
is the widening item W1; shipping unverified operations alongside verified
ones would blur the theorem inventory.
-/

namespace Shallot

/-- Three-way comparison result (own type — extractable subset). -/
inductive Cmp where
  | lt
  | eq
  | gt

def cmpChar (a b : Char) : Cmp :=
  if Nat.blt a.toNat b.toNat then .lt
  else if Nat.blt b.toNat a.toNat then .gt
  else .eq

def cmpChars : List Char → List Char → Cmp
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmpChar a b with
    | .lt => .lt
    | .gt => .gt
    | .eq => cmpChars as bs

/-- Lexicographic string comparison through codepoints. -/
def cmpStr (a b : String) : Cmp :=
  cmpChars a.toList b.toList

inductive RBColor where
  | red
  | black

inductive RBNode (α : Type) where
  | leaf
  | node (c : RBColor) (l : RBNode α) (k : String) (v : α) (r : RBNode α)

namespace RBNode

def find? {α : Type} : RBNode α → String → Option α
  | .leaf, _ => none
  | .node _ l k v r, key =>
    match cmpStr key k with
    | .lt => find? l key
    | .gt => find? r key
    | .eq => some v

/-- Okasaki's balance: rebuild any black-grandparent/red-parent/red-child
configuration into a red node with two black children. -/
def balance {α : Type} (c : RBColor) (l : RBNode α) (k : String) (v : α) (r : RBNode α) :
    RBNode α :=
  match c, l, k, v, r with
  | .black, .node .red (.node .red a xk xv b) yk yv c', zk, zv, d =>
    .node .red (.node .black a xk xv b) yk yv (.node .black c' zk zv d)
  | .black, .node .red a xk xv (.node .red b yk yv c'), zk, zv, d =>
    .node .red (.node .black a xk xv b) yk yv (.node .black c' zk zv d)
  | .black, a, xk, xv, .node .red (.node .red b yk yv c') zk zv d =>
    .node .red (.node .black a xk xv b) yk yv (.node .black c' zk zv d)
  | .black, a, xk, xv, .node .red b yk yv (.node .red c' zk zv d) =>
    .node .red (.node .black a xk xv b) yk yv (.node .black c' zk zv d)
  | c, l, k, v, r => .node c l k v r

def ins {α : Type} (key : String) (val : α) : RBNode α → RBNode α
  | .leaf => .node .red .leaf key val .leaf
  | .node c l k v r =>
    match cmpStr key k with
    | .lt => balance c (ins key val l) k v r
    | .gt => balance c l k v (ins key val r)
    | .eq => .node c l key val r

def blacken {α : Type} : RBNode α → RBNode α
  | .leaf => .leaf
  | .node _ l k v r => .node .black l k v r

def insert {α : Type} (t : RBNode α) (key : String) (val : α) : RBNode α :=
  blacken (ins key val t)

def fromList {α : Type} : List (String × α) → RBNode α
  | [] => .leaf
  | (k, v) :: rest => insert (fromList rest) k v

def toList {α : Type} : RBNode α → List (String × α)
  | .leaf => []
  | .node _ l k v r => toList l ++ (k, v) :: toList r

def size {α : Type} : RBNode α → Nat
  | .leaf => 0
  | .node _ l _ _ r => 1 + size l + size r

def contains {α : Type} (t : RBNode α) (key : String) : Bool :=
  match find? t key with
  | some _ => true
  | none => false

end RBNode

/-- Plain association-list lookup — the MODEL for R6 refinement. -/
def assocLookup {α : Type} : List (String × α) → String → Option α
  | [], _ => none
  | (k, v) :: rest, key =>
    match cmpStr key k with
    | .eq => some v
    | _ => assocLookup rest key

end Shallot
