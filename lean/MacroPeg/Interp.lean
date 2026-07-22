import MacroPeg.Syntax

/-!
# Macro PEG interpreter (fuel-based, total)

Mirrors `MDerives` 1:1, exactly as `Shallot.Peg.Interp.pegRun` mirrors
`Derives` — now parameterized by `Strategy`, mutual with `evalArgsPar` and
`evalArgsSeq` (the `.callByValuePar` / `.callByValueSeq` argument-evaluation
helpers). Same project-wide fuel convention: `none` means "out of fuel" and
nothing else; `some .fail` is a legitimate semantic outcome.

The `.call` case dispatches on `s`. Under `.callByName` it is structurally
identical to `.nt` in `pegRun`: look up the rule, recurse into the
(substituted) body at fuel `f` — matching `MDerives.callNameOk`/
`callNameFail`. Under `.callByValuePar`, `evalArgsPar` first evaluates every
actual parameter against the SAME `input` (never threading it — matching
`MDerives.DerivesArgsPar`); `some none` (some argument failed) becomes
`some .fail` for the call, `some (some vals)` recurses into the substituted
body from the UNCHANGED `input`, matching `MDerives.callParOk`/
`callParFail`/`callParArgFail`. Under `.callByValueSeq`, `evalArgsSeq`
evaluates the actual parameters SEQUENTIALLY, THREADING the input through
them (matching `MDerives.DerivesArgsSeq`); `some none` (some argument
failed) becomes `some .fail`, and `some (some (vals, mid))` recurses into
the substituted body from `mid` — the FINAL threaded position, NOT the
original `input` — matching `MDerives.callSeqOk`/`callSeqFail`/
`callSeqArgFail`.

`.param k` has a dead `some .fail` branch, exactly like `pegRun`'s dead
inner-`star` branch: unreachable once `subst` has fired at the enclosing
`call` (see `MacroPeg/Syntax.lean`), kept only so the pattern match is total.
-/

namespace Shallot.MacroPeg

/-- Monomorphic "prefix consumed before this known suffix" — computes `p`
such that `input = p ++ rest`, by walking `input` and comparing lengths at
each step (own recursion, not `List.take`, per the monomorphic-helpers
discipline; mirrors `mderives_suffix`'s existential on the `Derives`/proof
side, made computable here for the interpreter). If `rest` is not actually
a suffix of `input`, this still returns a defined (if meaningless) value —
callers here only ever apply it to a `rest` that `mpegRun` itself just
produced from `input`, so it is always a genuine suffix in practice. -/
def prefixBeforeSuffix : List Char → List Char → List Char
  | input, rest =>
    if lenChars input == lenChars rest then []
    else
      match input with
      | [] => []
      | c :: cs => c :: prefixBeforeSuffix cs rest

mutual

def mpegRun (g : MGrammar) (s : Strategy) : Nat → MExp → List Char → Option MOutcome
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
    | .lit str =>
      match stripPrefix? str input with
      | some rest => some (.ok (.leaf str) rest)
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
          match s with
          | .callByName =>
            match mpegRun g s fuel (MExp.subst args r.body) input with
            | some (.ok t rest) => some (.ok (.nodeCall i t) rest)
            | some .fail => some .fail
            | none => none
          | .callByValuePar =>
            match evalArgsPar g s fuel input args with
            | none => none
            | some none => some .fail
            | some (some vals) =>
              match mpegRun g s fuel (MExp.subst vals r.body) input with
              | some (.ok t rest) => some (.ok (.nodeCall i t) rest)
              | some .fail => some .fail
              | none => none
          | .callByValueSeq =>
            match evalArgsSeq g s fuel input args with
            | none => none
            | some none => some .fail
            | some (some (vals, mid)) =>
              match mpegRun g s fuel (MExp.subst vals r.body) mid with
              | some (.ok t rest) => some (.ok (.nodeCall i t) rest)
              | some .fail => some .fail
              | none => none
        else some .fail
    | .seq e₁ e₂ =>
      match mpegRun g s fuel e₁ input with
      | some (.ok t₁ rest₁) =>
        match mpegRun g s fuel e₂ rest₁ with
        | some (.ok t₂ rest₂) => some (.ok (.seq t₁ t₂) rest₂)
        | some .fail => some .fail
        | none => none
      | some .fail => some .fail
      | none => none
    | .alt e₁ e₂ =>
      match mpegRun g s fuel e₁ input with
      | some (.ok t rest) => some (.ok (.choiceL t) rest)
      | some .fail =>
        match mpegRun g s fuel e₂ input with
        | some (.ok t rest) => some (.ok (.choiceR t) rest)
        | some .fail => some .fail
        | none => none
      | none => none
    | .star e =>
      match mpegRun g s fuel e input with
      | some (.ok t rest) =>
        match mpegRun g s fuel (.star e) rest with
        | some (.ok ts rest') => some (.ok (.starCons t ts) rest')
        | some .fail => some .fail -- semantically unreachable; kept for totality
        | none => none
      | some .fail => some (.ok .starNil input)
      | none => none
    | .notP e =>
      match mpegRun g s fuel e input with
      | some (.ok _ _) => some .fail
      | some .fail => some (.ok .notT input)
      | none => none
    | .dbg _ => some (.ok .dbgT input)

/-- `.callByValuePar` argument evaluation: every element of the list is run
against the SAME `input` (no threading). `none` = fuel ran out somewhere;
`some none` = at least one argument failed (so the whole call fails, see
`mpegRun`'s `.call` case); `some (some vals)` = all succeeded, `vals` the
`.lit`-wrapped consumed prefixes in order, ready to substitute via
`MExp.subst`. -/
def evalArgsPar (g : MGrammar) (s : Strategy) (fuel : Nat) (input : List Char) :
    List MExp → Option (Option (List MExp))
  | [] => some (some [])
  | a :: as =>
    match mpegRun g s fuel a input with
    | none => none
    | some .fail => some none
    | some (.ok _ rest) =>
      match evalArgsPar g s fuel input as with
      | none => none
      | some none => some none
      | some (some vs) => some (some (.lit (prefixBeforeSuffix input rest) :: vs))

/-- `.callByValueSeq` argument evaluation: the arguments are run
SEQUENTIALLY and the input is THREADED — `a` is run against `input`, then
the remaining `as` are run against `rest` (the position `a` left off at),
and so on. `none` = fuel ran out somewhere; `some none` = some argument
failed (so the whole call fails, see `mpegRun`'s `.call` case); `some (some
(vals, final))` = all succeeded, `vals` the `.lit`-wrapped consumed prefixes
in order (each prefix taken relative to the position that argument started
at), and `final` the input remaining after the WHOLE list was threaded
through — the position `mpegRun` then derives the callee body from, unlike
`evalArgsPar` which returns no threaded remainder. -/
def evalArgsSeq (g : MGrammar) (s : Strategy) (fuel : Nat) (input : List Char) :
    List MExp → Option (Option (List MExp × List Char))
  | [] => some (some ([], input))
  | a :: as =>
    match mpegRun g s fuel a input with
    | none => none
    | some .fail => some none
    | some (.ok _ rest) =>
      match evalArgsSeq g s fuel rest as with
      | none => none
      | some none => some none
      | some (some (vs, final)) =>
        some (some (.lit (prefixBeforeSuffix input rest) :: vs, final))

end

end Shallot.MacroPeg
