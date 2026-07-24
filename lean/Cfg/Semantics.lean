import Cfg.Syntax

/-!
# Context-free grammar generation semantics

Generation is defined directly in "resolve this nonterminal fully, then its
symbols left to right" order, rather than via general sentential-form
rewriting plus a separate "leftmost" restriction. This coincides with the
textbook rewriting-based definition of `L(G)` — a completely standard fact,
not re-derived here (nothing downstream needs the rewriting-sequence view,
only the yielded-string-set view) — and it is exactly the shape
`cfg_cps_complete` (`Cfg/Cps.lean`) needs for its induction, mirroring how
`Derives.seqOk` (`Shallot/Peg/Semantics.lean`) derives `e₁` fully before
`e₂`.

`Language`/`IsCFL` are kept LOCAL to this piece — this is not a claim of a
project-wide `Language` abstraction; T4–T6 (out of scope this round) are
free to introduce their own if/when needed.
-/

namespace Shallot.Cfg

mutual
  /-- Nonterminal `i` generates string `w`: expand into one alternative
  (`hmem : rhs ∈ alts`), then resolve each symbol of that alternative left to
  right via `GenRhs`. -/
  inductive Gen (g : CFGrammar) : Nat → List Char → Prop where
    | prod (i : Nat) (alts : List Rhs) (rhs : List Sym) (w : List Char)
        (halts : altsAt g.rules i = some alts) (hmem : rhs ∈ alts)
        (hrhs : GenRhs g rhs w) :
        Gen g i w

  inductive GenRhs (g : CFGrammar) : List Sym → List Char → Prop where
    | nil : GenRhs g [] []
    | cons_t (c : Char) (rest : List Sym) (w : List Char)
        (h : GenRhs g rest w) :
        GenRhs g (.t c :: rest) (c :: w)
    | cons_nt (j : Nat) (rest : List Sym) (w₁ w₂ : List Char)
        (h₁ : Gen g j w₁) (h₂ : GenRhs g rest w₂) :
        GenRhs g (.nt j :: rest) (w₁ ++ w₂)
end

abbrev Language := List Char → Prop

def CFGrammar.language (g : CFGrammar) : Language := fun w => Gen g g.start w

def IsCFL (L : Language) : Prop := ∃ g : CFGrammar, ∀ w, L w ↔ g.language w

end Shallot.Cfg
