/-!
# Context-free grammar syntax

Formalizes plain context-free grammars (CFG), needed for T2 (`CFL ⊆
MPEL^CBN_1`, `Cfg/Cps.lean`) — nothing like this existed anywhere in the
project before (confirmed via repo-wide grep). Deliberately hand-rolled
rather than reusing `Mathlib.Computability.ContextFreeGrammar` (which does
exist, but adopting it would be this project's first-ever external
dependency, for essentially no proof-content benefit: Mathlib's CFG module
has no GNF/Chomsky normal form and no pumping lemma either, and its
`Finset`-based rules would fight this project's uniform `List`-based,
index-keyed, no-typeclass-search style).

Design, continuing `Shallot.Peg`/`Shallot.MacroPeg`'s conventions:
- nonterminals are `Nat` indices (mirrors `PExp.nt`/`MExp.call`), terminals
  are `Char` — no `Symbol T N` sum-over-arbitrary-types
- `CFGrammar.rules : List (List Rhs)` groups alternatives by nonterminal
  index, one slot per index (mirrors `MGrammar.rules : List MRule`, "one
  body per index," rather than a flat, ungrouped `(nonterminal, rhs)` list).
  A nonterminal with `[]` alternatives simply never generates anything — no
  separate "undefined nonterminal" failure mode is needed.
- the type itself is a GENERAL (unrestricted) CFG — Greibach Normal Form
  (GNF) is a separate, decidable `Bool` predicate (`isGnfB`), not baked into
  the type, mirroring `acyclicB`'s style in `MacroPeg/CallGraph.lean`. T2's
  headline theorems take `isGnfB g = true` as an explicit HYPOTHESIS, the
  same way `MExp.expand` takes `acyclicB g = true` — general CFG-to-GNF
  normalization (eliminating ε-productions, unit productions, left
  recursion) is classical (Greibach 1965 / Hopcroft–Ullman) and is NOT
  formalized here; it is cited, not re-derived, and is never smuggled in as
  an unproven declaration or placeholder gap (this project's policy forbids
  both, even as stand-ins).
- **`isGnfB` forbids BARE ε ANYWHERE** (every alternative, for every
  nonterminal including the start symbol, must have a leading terminal) —
  stricter than the textbook convention that allows a single `S → ε`
  exception for the start symbol. This is a deliberate strengthening, not an
  oversight: discovered mid-proof (spiking `cfg_cps_sound`'s termination
  argument) that allowing ε ANYWHERE — even only at the start symbol in the
  textbook's restricted sense — reopens the door to a chain of
  zero-consumption nonterminal delegations if the start symbol can be
  reached again via some other production's argument threading, which
  breaks the clean "every nonterminal call strictly decreases remaining
  input length" termination measure the CPS embedding's totality proof
  relies on. Consequence, stated honestly rather than glossed over: this
  formalizes CFL membership for the language MINUS the empty string (i.e.
  `L(g) \ {ε}`); folding `ε ∈ L(G)` back in is a trivial, separate
  top-level Boolean flag (checked once, outside the grammar/derivation
  machinery entirely) and is not needed for T2's headline (`CFL ⊆
  MPEL^CBN_1`), since every CFL is trivially the union of its
  ε-free part and (possibly) `{ε}`.
-/

namespace Shallot.Cfg

/-- One right-hand-side symbol: a terminal character or a nonterminal
index. -/
inductive Sym where
  | t (c : Char)
  | nt (i : Nat)
  deriving DecidableEq

/-- One production's right-hand side; `[]` is the ε-production. General
(unrestricted) shape — GNF-ness is checked separately, below, not baked into
this type, so `CFGrammar` can faithfully state the textbook notion of CFL
before any normalization. -/
abbrev Rhs := List Sym

structure CFGrammar where
  rules : List (List Rhs)
  start : Nat

/-- Monomorphic alternative-list lookup for nonterminal `i` (mirrors
`ruleAt`/`ruleAtM`). -/
def altsAt : List (List Rhs) → Nat → Option (List Rhs)
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, n + 1 => altsAt rs n

/-! ## Greibach Normal Form, as a decidable `Bool` predicate

Not a type-level restriction — see the module docstring. `isGnfB g = true`
is the explicit hypothesis T2's headline theorems carry. -/

def symIsNt : Sym → Bool
  | .nt _ => true
  | .t _ => false

/-- A single `Rhs` is GNF-shaped: NON-EMPTY, `.t _ :: rest` with every
element of `rest` a nonterminal (no terminal anywhere but the head, no bare
ε — see the module docstring on why ε is disallowed everywhere, not just
outside the start symbol). -/
def rhsIsGnfB : Rhs → Bool
  | [] => false
  | .t _ :: rest => rest.all symIsNt
  | .nt _ :: _ => false

def isGnfB (g : CFGrammar) : Bool :=
  g.rules.all (fun alts => alts.all rhsIsGnfB)

/-- For a GNF-shaped `Rhs`, the nonterminal sequence following the leading
terminal. -/
def ntSeq : Rhs → List Nat
  | [] => []
  | .nt j :: rest => j :: ntSeq rest
  | .t _ :: rest => ntSeq rest -- dead under `isGnfB g = true`

/-- For a GNF-shaped `Rhs`: `some (c, js)` for `.t c :: rest` with `js` the
nonterminal sequence in `rest` — the only reachable case once `isGnfB g =
true` (ε is disallowed entirely; see the module docstring). The `[]`/`.nt _
:: _` arms are dead under that hypothesis (kept for totality, like
`pegRun`'s dead star-fail branch). -/
def gnfHead : Rhs → Option (Char × List Nat)
  | [] => none
  | .t c :: rest => some (c, ntSeq rest)
  | .nt _ :: _ => none

end Shallot.Cfg
