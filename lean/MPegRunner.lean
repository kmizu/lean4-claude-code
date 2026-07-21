import MacroPeg.Corpus

/-!
# mpeg-runner — differential harness, Lean side (Macro PEG)

Mirrors `Runner.lean`: evaluates `Shallot.MacroPeg.mCases` natively and
emits canonical JSONL. The Scala CLI's `macro-dump` subcommand does the
same over the *extracted* table.
-/

def mpegJsonlLine (id result : String) : String :=
  "{\"case\":\"" ++ id ++ "\",\"phase\":\"eval\",\"status\":\"ok\",\"result\":\"" ++ result ++ "\"}"

def main (args : List String) : IO UInt32 := do
  let lines := Shallot.MacroPeg.mCases.map fun (id, result) => mpegJsonlLine id result
  let text := String.intercalate "\n" lines ++ "\n"
  match args with
  | out :: _ => IO.FS.writeFile out text
  | [] => IO.print text
  return 0
