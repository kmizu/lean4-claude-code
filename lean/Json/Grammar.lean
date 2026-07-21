import Shallot.Peg.Syntax
import Shallot.Peg.Interp

/-!
# RFC 8259, as a PEG value

The grammar mirrors the RFC's ABNF rule-for-rule — including its whitespace
discipline (`begin-object = ws %x7B ws` etc.; whitespace lives INSIDE the
structural tokens, values themselves are bare). The correspondence:

| RFC 8259 ABNF                          | here                       |
|----------------------------------------|----------------------------|
| `JSON-text = ws value ws`              | rule 1 (`+ !.` for EOF)    |
| `value = false / null / true / object / array / number / string` | rule 2, same order |
| `begin-object = ws %x7B ws` (etc.)     | `beginObject` … PExp defs  |
| `object = begin-object [ member *( value-separator member ) ] end-object` | rule 3 |
| `member = string name-separator value` | rule 4                     |
| `array = begin-array [ value *( value-separator value ) ] end-array` | rule 5 |
| `string = quotation-mark *char quotation-mark` | rule 6             |
| `char = unescaped / escape (…)`        | rules 7–8                  |
| `number = [ minus ] int [ frac ] [ exp ]` | rule 9                  |
| `int = zero / ( digit1-9 *DIGIT )`     | rule 10                    |
| `frac = decimal-point 1*DIGIT`         | rule 11                    |
| `exp = e [ minus / plus ] 1*DIGIT`     | rule 12                    |
| `HEXDIG`                               | rule 13                    |
| `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF` | three `range`s      |

ABNF's ordered-choice-free alternatives are written as PEG prioritized
choice in the SAME order; every pair of `value` alternatives is disjoint on
its first character, so prioritization does not change the language.
Because parsing is the verified `pegRun`, soundness/completeness/
determinism (T1–T3) hold for this grammar by instantiation.

Note on surrogates: our `Char` is a Unicode scalar value, so inputs can
never contain lone surrogates — `%x5D-10FFFF` over scalar values is
exactly the last `range`.
-/

namespace Shallot.Json

namespace JNT

def ws : Nat := 0
def jsonText : Nat := 1
def value : Nat := 2
def object : Nat := 3
def member : Nat := 4
def array : Nat := 5
def string : Nat := 6
def char : Nat := 7
def escape : Nat := 8
def number : Nat := 9
def int : Nat := 10
def frac : Nat := 11
def exp : Nat := 12
def hex : Nat := 13

end JNT

/-- `DIGIT` -/
def digitP : PExp := .range '0' '9'

/-- `digit1-9` -/
def digit19P : PExp := .range '1' '9'

/-- `begin-object = ws %x7B ws` — RFC keeps whitespace inside the
structural tokens; values themselves are bare. -/
def structTok (c : Char) : PExp :=
  .seq (.nt JNT.ws) (.seq (.chr c) (.nt JNT.ws))

def beginObjectP : PExp := structTok '{'
def endObjectP : PExp := structTok '}'
def beginArrayP : PExp := structTok '['
def endArrayP : PExp := structTok ']'
def nameSepP : PExp := structTok ':'
def valueSepP : PExp := structTok ','

/-- `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF` -/
def unescapedP : PExp :=
  .alt (.range ' ' '!')
    (.alt (.range '#' '[')
      (.range ']' (Char.ofNat 0x10FFFF)))

def jsonRules : List PExp :=
  [ -- 0 ws = *( %x20 / %x09 / %x0A / %x0D )
    .star (.alt (.chr ' ') (.alt (.chr '\t') (.alt (.chr '\n') (.chr '\r')))),
    -- 1 JSON-text = ws value ws  (+ end of input)
    .seq (.nt JNT.ws)
      (.seq (.nt JNT.value) (.seq (.nt JNT.ws) (.notP .any))),
    -- 2 value = false / null / true / object / array / number / string
    .alt (.lit "false".toList)
      (.alt (.lit "null".toList)
        (.alt (.lit "true".toList)
          (.alt (.nt JNT.object)
            (.alt (.nt JNT.array)
              (.alt (.nt JNT.number) (.nt JNT.string)))))),
    -- 3 object = begin-object [ member *( value-separator member ) ] end-object
    .seq beginObjectP
      (.seq (PExp.opt (.seq (.nt JNT.member)
                        (.star (.seq valueSepP (.nt JNT.member)))))
        endObjectP),
    -- 4 member = string name-separator value
    .seq (.nt JNT.string) (.seq nameSepP (.nt JNT.value)),
    -- 5 array = begin-array [ value *( value-separator value ) ] end-array
    .seq beginArrayP
      (.seq (PExp.opt (.seq (.nt JNT.value)
                        (.star (.seq valueSepP (.nt JNT.value)))))
        endArrayP),
    -- 6 string = quotation-mark *char quotation-mark
    .seq (.chr '"') (.seq (.star (.nt JNT.char)) (.chr '"')),
    -- 7 char = unescaped / escape-sequence
    .alt unescapedP (.seq (.chr '\\') (.nt JNT.escape)),
    -- 8 escape = " / \ / '/' / b / f / n / r / t / u 4HEXDIG
    .alt (.chr '"')
      (.alt (.chr '\\')
        (.alt (.chr '/')
          (.alt (.chr 'b')
            (.alt (.chr 'f')
              (.alt (.chr 'n')
                (.alt (.chr 'r')
                  (.alt (.chr 't')
                    (.seq (.chr 'u')
                      (.seq (.nt JNT.hex)
                        (.seq (.nt JNT.hex)
                          (.seq (.nt JNT.hex) (.nt JNT.hex)))))))))))),
    -- 9 number = [ minus ] int [ frac ] [ exp ]
    .seq (PExp.opt (.chr '-'))
      (.seq (.nt JNT.int)
        (.seq (PExp.opt (.nt JNT.frac)) (PExp.opt (.nt JNT.exp)))),
    -- 10 int = zero / ( digit1-9 *DIGIT )
    .alt (.chr '0') (.seq digit19P (.star digitP)),
    -- 11 frac = decimal-point 1*DIGIT
    .seq (.chr '.') (.seq digitP (.star digitP)),
    -- 12 exp = e [ minus / plus ] 1*DIGIT
    .seq (.alt (.chr 'e') (.chr 'E'))
      (.seq (PExp.opt (.alt (.chr '-') (.chr '+')))
        (.seq digitP (.star digitP))),
    -- 13 HEXDIG (case-insensitive per RFC 5234)
    .alt digitP (.alt (.range 'a' 'f') (.range 'A' 'F')) ]

def jsonGrammar : Grammar :=
  { rules := jsonRules, start := JNT.jsonText }

/-! ## Smoke tests (accept / reject) -/

private def jOk (s : String) : Bool :=
  match pegRun jsonGrammar 100000 (.nt JNT.jsonText) s.toList with
  | some (.ok _ _) => true
  | _ => false

#guard jOk "true"
#guard jOk "null"
#guard jOk "  false  "
#guard jOk "42"
#guard jOk "-0.5e+10"
#guard jOk "0"
#guard jOk "\"hello\""
#guard jOk "\"esc \\n \\u00e9 \\uD83D\\uDE00\""
#guard jOk "[]"
#guard jOk "[ 1 , 2.5 , \"x\" ]"
#guard jOk "{}"
#guard jOk "{ \"a\" : [true, {\"b\": null}] , \"a\" : 0 }"

#guard !(jOk "")
#guard !(jOk "falsex")
#guard !(jOk "01")
#guard !(jOk "1.")
#guard !(jOk "1e")
#guard !(jOk "+1")
#guard !(jOk "[1,]")
#guard !(jOk "[1 2]")
#guard !(jOk "{\"a\":}")
#guard !(jOk "{'a':1}")
#guard !(jOk "\"unterminated")
#guard !(jOk "\"bad \\x escape\"")
#guard !(jOk "[1] extra")

end Shallot.Json
