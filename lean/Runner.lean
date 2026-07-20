import Shallot.Corpus

/-!
# shallot-runner — differential harness, Lean side

Evaluates `Shallot.cases` natively and emits canonical JSONL
(fixed key order: case, phase, status, result). The Scala CLI's `dump`
subcommand does the same over the *extracted* table.
-/

def jsonlLine (id result : String) : String :=
  "{\"case\":\"" ++ id ++ "\",\"phase\":\"eval\",\"status\":\"ok\",\"result\":\"" ++ result ++ "\"}"

def main (args : List String) : IO UInt32 := do
  let lines := Shallot.cases.map fun (id, result) => jsonlLine id result
  let text := String.intercalate "\n" lines ++ "\n"
  match args with
  | out :: _ => IO.FS.writeFile out text
  | [] => IO.print text
  return 0
