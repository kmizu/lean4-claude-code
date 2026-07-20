import Lens.Pipeline

/-!
# Lens golden tests (`lake test`)

Extracts the default roots from the compiled `Shallot` module and diffs the
generated Scala against `tests/golden/Shallot.scala`. Update the golden with
`LENS_UPDATE_GOLDEN=1 lake test` (then review the git diff!).

Runs with cwd = the lake package directory (`lean/`).
-/

def goldenFile : System.FilePath := "tests" / "golden" / "Shallot.scala"

def firstDiffLine (a b : List String) : Option (Nat × String × String) :=
  let rec go (i : Nat) : List String → List String → Option (Nat × String × String)
    | [], [] => none
    | x :: xs, y :: ys => if x == y then go (i + 1) xs ys else some (i, x, y)
    | x :: _, [] => some (i, x, "<EOF>")
    | [], y :: _ => some (i, "<EOF>", y)
  go 0 a b

def main : IO UInt32 := do
  match ← Lens.runPipeline `Shallot Lens.defaultRoots {} with
  | .error errs =>
    Lens.reportErrors errs
    return 1
  | .ok text =>
    if (← IO.getEnv "LENS_UPDATE_GOLDEN").isSome then
      IO.FS.createDirAll ("tests" / "golden")
      IO.FS.writeFile goldenFile text
      IO.println s!"lenstests: UPDATED {goldenFile} — review with git diff"
      return 0
    if !(← goldenFile.pathExists) then
      IO.eprintln s!"lenstests: missing golden file {goldenFile}; run LENS_UPDATE_GOLDEN=1 lake test"
      return 1
    let golden ← IO.FS.readFile goldenFile
    if golden == text then
      IO.println "lenstests: golden OK (extraction matches tests/golden/Shallot.scala)"
      return 0
    else
      match firstDiffLine (golden.splitOn "\n") (text.splitOn "\n") with
      | some (i, g, t) =>
        IO.eprintln s!"lenstests: golden MISMATCH at line {i + 1}:"
        IO.eprintln s!"  golden: {g}"
        IO.eprintln s!"  actual: {t}"
      | none =>
        IO.eprintln "lenstests: golden MISMATCH (content differs)"
      return 1
