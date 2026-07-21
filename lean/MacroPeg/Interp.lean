import MacroPeg.Syntax

/-!
# Macro PEG interpreter (fuel-based, total)

Mirrors `MDerives` 1:1, exactly as `Shallot.Peg.Interp.pegRun` mirrors
`Derives`. Same project-wide fuel convention: `none` means "out of fuel" and
nothing else; `some .fail` is a legitimate semantic outcome.

The `.call` case is structurally identical to `.nt` in `pegRun`: look up the
rule, recurse into its (substituted) body at fuel `f` — ONE decrement per
call, matching `MDerives.callOk`/`callFail`.

`.param k` has a dead `some .fail` branch, exactly like `pegRun`'s dead
inner-`star` branch: unreachable once `subst` has fired at the enclosing
`call` (see `MacroPeg/Syntax.lean`), kept only so the pattern match is total.
-/

namespace Shallot.MacroPeg

def mpegRun (g : MGrammar) : Nat → MExp → List Char → Option MOutcome
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
    | .param _ => some .fail -- unreachable once `subst` has fired; kept for totality
    | .call i args =>
      match ruleAtM g.rules i with
      | none => some .fail
      | some r =>
        -- Bool `==` (not Prop `≠`/`Decidable`) — Lens's builtin whitelist
        -- has `BEq.beq` for `Nat` but not `instDecidableNot`, matching how
        -- `.chr`/`.range` above use `beqChar`/`leChar` Bool conditions.
        if r.arity == args.length then
          match mpegRun g fuel (MExp.subst args r.body) input with
          | some (.ok t rest) => some (.ok (.nodeCall i t) rest)
          | some .fail => some .fail
          | none => none
        else some .fail
    | .seq e₁ e₂ =>
      match mpegRun g fuel e₁ input with
      | some (.ok t₁ rest₁) =>
        match mpegRun g fuel e₂ rest₁ with
        | some (.ok t₂ rest₂) => some (.ok (.seq t₁ t₂) rest₂)
        | some .fail => some .fail
        | none => none
      | some .fail => some .fail
      | none => none
    | .alt e₁ e₂ =>
      match mpegRun g fuel e₁ input with
      | some (.ok t rest) => some (.ok (.choiceL t) rest)
      | some .fail =>
        match mpegRun g fuel e₂ input with
        | some (.ok t rest) => some (.ok (.choiceR t) rest)
        | some .fail => some .fail
        | none => none
      | none => none
    | .star e =>
      match mpegRun g fuel e input with
      | some (.ok t rest) =>
        match mpegRun g fuel (.star e) rest with
        | some (.ok ts rest') => some (.ok (.starCons t ts) rest')
        | some .fail => some .fail -- semantically unreachable; kept for totality
        | none => none
      | some .fail => some (.ok .starNil input)
      | none => none
    | .notP e =>
      match mpegRun g fuel e input with
      | some (.ok _ _) => some .fail
      | some .fail => some (.ok .notT input)
      | none => none
    | .dbg _ => some (.ok .dbgT input)

end Shallot.MacroPeg
