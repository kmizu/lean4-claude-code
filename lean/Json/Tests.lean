import Json.ToAst
import Json.Printer

/-!
# Build-time checks: parse results and empirical roundtrips

Structure-level expectations plus print∘parse fixpoints. The roundtrip
THEOREM (J-RT) arrives in the proof milestone; these guards pin behavior
meanwhile (and forever, as regressions).
-/

namespace Shallot.Json

private def reprint (s : String) : Option String :=
  match parseJson 100000 s with
  | .ok v => some (printJson v)
  | .error _ => none

-- parse → print reaches the canonical form …
#guard reprint "  [ 1 , 2.50 , \"a\\u00e9b\" ]  " == some "[1,2.50,\"aéb\"]"
#guard reprint "{ \"k\" : { \"n\" : -0.5E+10 } }" == some "{\"k\":{\"n\":-0.5E+10}}"
#guard reprint "\"\\uD83D\\uDE00\"" == some "\"😀\""
#guard reprint "\"tab\\tnl\\n\"" == some "\"tab\\u0009nl\\u000a\""
#guard reprint "[[],{},[[]]]" == some "[[],{},[[]]]"
#guard reprint "3" == some "3"
#guard reprint "{\"a\":1,\"a\":2}" == some "{\"a\":1,\"a\":2}" -- duplicates preserved

-- … and the canonical form is a fixpoint (empirical roundtrip).
private def rtFix (s : String) : Bool :=
  match reprint s with
  | some c => reprint c == some c
  | none => false

#guard rtFix "  [ 1 , 2.50 , \"a\\u00e9b\", true, null ]  "
#guard rtFix "{ \"k\" : [ -0.5E+10, 1e-2, 0.0, \"\\\"quote\\\\back\\\" \\u0000\" ] }"
#guard rtFix "\"\\uD834\\uDD1E surrogate pair\""

-- Lone surrogates are REJECTED (documented implementation choice).
#guard (match parseJson 100000 "\"\\uD800\"" with
        | .error .loneSurrogate => true
        | _ => false)
#guard (match parseJson 100000 "\"\\uDC00 low first\"" with
        | .error .loneSurrogate => true
        | _ => false)

-- Number syntax is preserved verbatim (no normalization).
#guard reprint "[1e5,1E5,1e+5,1e-5,10.500]" == some "[1e5,1E5,1e+5,1e-5,10.500]"

end Shallot.Json
