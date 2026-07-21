import MacroPeg.Examples
import MacroPeg.Interp
import MacroPeg.Render

/-!
# Macro PEG differential corpus (single source of truth)

Mirrors `Shallot.Corpus`'s design: the case table is defined ONCE here and
**extracted** — the Lean runner evaluates it natively, the Scala CLI's
`macro-dump` subcommand evaluates the generated version. Any divergence is
extractor/runtime drift. Witnesses are the copy-language ones from
`NonTrivialLanguagesSpec.scala` (`kmizu/macro_peg`), the same grammar
`copy_language_ww` (`MacroPeg/Examples.lean`) proves for ALL `u`.
-/

namespace Shallot.MacroPeg

/-- `Copy("") !.` — full-string match, mirroring the Scala grammar's own
`S = Copy("") !.;` top rule (without the `!.` guard, `Copy("")` always has a
zero-consumption escape via its third alternative, so partial-prefix
"successes" would otherwise obscure genuine accept/reject). -/
def mCase (id : String) (input : String) : String × String :=
  (id, renderMPeg (mpegRun copyGrammar 500 (.seq (.call copyIdx [.lit []]) (.notP .any)) input.toList))

def mCases : List (String × String) :=
  [ mCase "300-mpeg-copy-empty" "",
    mCase "301-mpeg-copy-aa" "aa",
    mCase "302-mpeg-copy-bb" "bb",
    mCase "303-mpeg-copy-abab" "abab",
    mCase "304-mpeg-copy-aabbaabb" "aabbaabb",
    mCase "305-mpeg-copy-reject-ab" "ab",
    mCase "306-mpeg-copy-reject-aba" "aba",
    mCase "307-mpeg-copy-reject-abba" "abba" ]

end Shallot.MacroPeg
