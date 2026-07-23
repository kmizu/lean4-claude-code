import MacroPeg.Examples
import MacroPeg.Interp
import MacroPeg.Render

/-!
# Macro PEG differential corpus (single source of truth)

Mirrors `Shallot.Corpus`'s design: the case table is defined ONCE here and
**extracted** — the Lean runner evaluates it natively, the Scala CLI's
`macro-dump` subcommand evaluates the generated version. Any divergence is
extractor/runtime drift. `CallByName` witnesses are the copy-language ones
from `NonTrivialLanguagesSpec.scala` (`kmizu/macro_peg`), the same grammar
`copy_language_ww` (`MacroPeg/Examples.lean`) proves for ALL `u`.
`CallByValuePar` witnesses mirror `MacroPegCallByValueParSpec.scala`'s
`F(A) = A A A` example (same grammar as `Examples.lean`'s `#guard` smoke
tests, `parFGrammar`). `CallByValueSeq` witnesses mirror
`MacroPegCallByValueSeqSpec.scala`'s `F(A, B, C) = A B C` example
(`seqFGrammar`).
-/

namespace Shallot.MacroPeg

/-- `Copy("") !.` — full-string match, mirroring the Scala grammar's own
`S = Copy("") !.;` top rule (without the `!.` guard, `Copy("")` always has a
zero-consumption escape via its third alternative, so partial-prefix
"successes" would otherwise obscure genuine accept/reject). -/
def mCase (id : String) (input : String) : String × String :=
  (id, renderMPeg
    (mpegRun copyGrammar .callByName 500 (.seq (.call copyIdx [.lit []]) (.notP .any)) input.toList))

/-- `F("a") !.` under `.callByValuePar` — mirrors `parFGrammar`'s `#guard`
smoke tests in `Examples.lean`. -/
def mParCase (id : String) (input : String) : String × String :=
  (id, renderMPeg
    (mpegRun parFGrammar .callByValuePar 500 (.seq (.call parFIdx [.lit ['a']]) (.notP .any)) input.toList))

/-- `F("a", "b", "c") !.` under `.callByValueSeq` — mirrors `seqFGrammar`'s
`#guard` smoke tests in `Examples.lean`. -/
def mSeqCase (id : String) (input : String) : String × String :=
  (id, renderMPeg
    (mpegRun seqFGrammar .callByValueSeq 500
      (.seq (.call seqFIdx [.lit ['a'], .lit ['b'], .lit ['c']]) (.notP .any)) input.toList))

/-- `Double(Plus1, "aa") !.` (M-PEG-4, named-rule-as-value) — mirrors
`doubleHofGrammar`'s `#guard` smoke tests in `Examples.lean`. -/
def mHofDoubleCase (id : String) (input : String) : String × String :=
  (id, renderMPeg
    (mpegRun doubleHofGrammar .callByName 500
      (.seq (.call doubleHofIdx [.lam 1 plus1Body, .lit ['a', 'a']]) (.notP .any)) input.toList))

/-- `Map2((x,y -> x y x), "a", "b") !.` (M-PEG-4, lambda literal, arity 2) —
mirrors `map2Grammar`'s `#guard` smoke tests in `Examples.lean`. -/
def mHofMap2Case (id : String) (input : String) : String × String :=
  (id, renderMPeg
    (mpegRun map2Grammar .callByName 500
      (.seq (.call map2Idx [.lam 2 xyxBody, .lit ['a'], .lit ['b']]) (.notP .any)) input.toList))

/-- `Apply(Baz((x -> x)), "a") !.` (closure returned from `Baz` then
reapplied inside `Apply` — always fails) — mirrors `closureReturnGrammar`'s
`#guard` smoke test in `Examples.lean`. -/
def mHofReturnCase (id : String) (input : String) : String × String :=
  (id, renderMPeg
    (mpegRun closureReturnGrammar .callByName 500
      (.seq (.call closureReturnApplyIdx
        [.call closureReturnBazIdx [.lam 1 (.param 0)], .lit ['a']]) (.notP .any)) input.toList))

def mCases : List (String × String) :=
  [ mCase "300-mpeg-copy-empty" "",
    mCase "301-mpeg-copy-aa" "aa",
    mCase "302-mpeg-copy-bb" "bb",
    mCase "303-mpeg-copy-abab" "abab",
    mCase "304-mpeg-copy-aabbaabb" "aabbaabb",
    mCase "305-mpeg-copy-reject-ab" "ab",
    mCase "306-mpeg-copy-reject-aba" "aba",
    mCase "307-mpeg-copy-reject-abba" "abba",
    mParCase "310-mpeg-par-f-aaa" "aaa",
    mParCase "311-mpeg-par-f-reject-aab" "aab",
    mParCase "312-mpeg-par-f-reject-aa" "aa",
    mSeqCase "320-mpeg-seq-f-abcabc" "abcabc",
    mSeqCase "321-mpeg-seq-f-reject-abcabx" "abcabx",
    mSeqCase "322-mpeg-seq-f-reject-abc" "abc",
    mHofDoubleCase "330-mpeg-hof-double-aaaaaaaa" "aaaaaaaa",
    mHofDoubleCase "331-mpeg-hof-double-reject-aaaa" "aaaa",
    mHofMap2Case "332-mpeg-hof-map2-aba" "aba",
    mHofMap2Case "333-mpeg-hof-map2-reject-abx" "abx",
    mHofMap2Case "334-mpeg-hof-map2-reject-ab" "ab",
    mHofReturnCase "335-mpeg-hof-return-reject-a" "a" ]

end Shallot.MacroPeg
