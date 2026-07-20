import Shallot.Peg.Syntax

/-!
# PEG interpreter (fuel-based, total)

Mirrors the `Derives` rules 1:1. Project-wide fuel convention: `none` means
"out of fuel" and NOTHING else; `some .fail` is a legitimate semantic
outcome. Every recursive call decrements fuel, so this is plain structural
recursion on `Nat` — extraction-friendly and proof-friendly (T0 fuel
monotonicity, then T1/T2/T3 in M4).

Note the dead `some .fail` branch in `star`: semantically a star never
fails (`starNeverFails` lemma in M4), but keeping the interpreter total and
syntax-directed costs nothing and keeps the T1 induction uniform.
-/

namespace Shallot

def pegRun (g : Grammar) : Nat → PExp → List Char → Option Outcome
  | 0, _, _ => none
  | fuel + 1, e, input =>
    match e with
    | .eps => some (.ok (.leaf []) input)
    | .any =>
      match input with
      | [] => some .fail
      | c :: rest => some (.ok (.leaf [c]) rest)
    | .chr c =>
      match input with
      | [] => some .fail
      | d :: rest => if beqChar c d then some (.ok (.leaf [d]) rest) else some .fail
    | .range lo hi =>
      match input with
      | [] => some .fail
      | d :: rest =>
        if leChar lo d && leChar d hi then some (.ok (.leaf [d]) rest) else some .fail
    | .lit s =>
      match stripPrefix? s input with
      | some rest => some (.ok (.leaf s) rest)
      | none => some .fail
    | .nt i =>
      match ruleAt g.rules i with
      | none => some .fail
      | some e' =>
        match pegRun g fuel e' input with
        | some (.ok t rest) => some (.ok (.nodeNT i t) rest)
        | some .fail => some .fail
        | none => none
    | .seq e₁ e₂ =>
      match pegRun g fuel e₁ input with
      | some (.ok t₁ rest₁) =>
        match pegRun g fuel e₂ rest₁ with
        | some (.ok t₂ rest₂) => some (.ok (.seq t₁ t₂) rest₂)
        | some .fail => some .fail
        | none => none
      | some .fail => some .fail
      | none => none
    | .alt e₁ e₂ =>
      match pegRun g fuel e₁ input with
      | some (.ok t rest) => some (.ok (.choiceL t) rest)
      | some .fail =>
        match pegRun g fuel e₂ input with
        | some (.ok t rest) => some (.ok (.choiceR t) rest)
        | some .fail => some .fail
        | none => none
      | none => none
    | .star e =>
      match pegRun g fuel e input with
      | some (.ok t rest) =>
        match pegRun g fuel (.star e) rest with
        | some (.ok ts rest') => some (.ok (.starCons t ts) rest')
        | some .fail => some .fail -- semantically unreachable; kept for totality
        | none => none
      | some .fail => some (.ok .starNil input)
      | none => none
    | .notP e =>
      match pegRun g fuel e input with
      | some (.ok _ _) => some .fail
      | some .fail => some (.ok .notT input)
      | none => none

end Shallot
