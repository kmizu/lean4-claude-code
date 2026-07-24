import MacroPeg.CounterexampleCorpus

/-!
# counterexample-runner — differential harness, Lean side (counterexamples)

Mirrors `MPegRunner.lean`: evaluates `Shallot.MacroPeg.ceCases` natively
and emits canonical JSONL. The Scala CLI's `macro-peg-diff` module runs
the SAME three grammars against the live reference `Evaluator`
independently (not against extracted code — the point of this corpus is
cross-checking against the reference implementation itself).
-/

def ceJsonlLine (id result : String) : String :=
  "{\"case\":\"" ++ id ++ "\",\"phase\":\"eval\",\"status\":\"ok\",\"result\":\"" ++ result ++ "\"}"

def main (args : List String) : IO UInt32 := do
  let lines := Shallot.MacroPeg.ceCases.map fun (id, result) => ceJsonlLine id result
  let text := String.intercalate "\n" lines ++ "\n"
  match args with
  | out :: _ => IO.FS.writeFile out text
  | [] => IO.print text
  return 0
