import Json

/-!
# json-suite — JSONTestSuite runner, Lean side

Runs the vendored nst/JSONTestSuite `test_parsing` corpus through the
verified JSON parser and emits one verdict line per file. The Scala CLI's
`json-suite` subcommand does the same over the EXTRACTED parser; the two
outputs are diffed, and `y_`/`n_` expectations are checked, by
`scripts/json-suite.sh`.

Files may be deliberately invalid UTF-8 — those are read as bytes and
rejected as `invalid-utf8` on BOTH sides (same strict-decode convention).
-/

open Shallot.Json

def verdict (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | none => "reject:invalid-utf8"
  | some s =>
    match parseJson 10000000 s with
    | .ok _ => "accept"
    | .error e => "reject:" ++ e.render

def main (args : List String) : IO UInt32 := do
  match args with
  | dir :: rest => do
    let entries ← System.FilePath.readDir dir
    let files := (entries.map (·.fileName)).filter (·.endsWith ".json")
    let sorted := files.qsort (fun a b => decide (a < b))
    let mut lines : Array String := #[]
    for f in sorted do
      let bytes ← IO.FS.readBinFile (System.FilePath.mk dir / f)
      lines := lines.push ("{\"file\":\"" ++ f ++ "\",\"verdict\":\"" ++ verdict bytes ++ "\"}")
    let text := String.intercalate "\n" lines.toList ++ "\n"
    match rest with
    | out :: _ => IO.FS.writeFile out text
    | [] => IO.print text
    return 0
  | _ =>
    IO.eprintln "usage: json-suite <dir> [outfile]"
    return 2
