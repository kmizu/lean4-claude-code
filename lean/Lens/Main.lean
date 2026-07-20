import Lens.Pipeline

/-!
# Lens CLI

```
lake exe extract -- [--out DIR] [--pkg PKG] [--module NAME] [--root NAME]...
```

All-or-nothing: on any translation error, every error is reported and no
file is touched. On success the output directory's `*.scala` files are
replaced atomically-ish (clear then write) — Lens owns that directory.
-/

open Lean

structure CliArgs where
  out : Option String := none
  pkg : String := "shallot.gen"
  module : Name := `Shallot
  roots : List Name := []

partial def parseArgs : List String → CliArgs → Except String CliArgs
  | [], acc => .ok acc
  | "--" :: rest, acc => parseArgs rest acc
  | "--out" :: v :: rest, acc => parseArgs rest { acc with out := some v }
  | "--pkg" :: v :: rest, acc => parseArgs rest { acc with pkg := v }
  | "--module" :: v :: rest, acc => parseArgs rest { acc with module := v.toName }
  | "--root" :: v :: rest, acc => parseArgs rest { acc with roots := acc.roots ++ [v.toName] }
  | arg :: _, _ => .error s!"unknown argument '{arg}'"

def clearScalaFiles (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then
    for entry in ← dir.readDir do
      if entry.path.extension == some "scala" then
        IO.FS.removeFile entry.path

def main (args : List String) : IO UInt32 := do
  let cli ← match parseArgs args {} with
    | .ok c => pure c
    | .error msg => IO.eprintln s!"lens: {msg}"; return 2
  let roots := if cli.roots.isEmpty then Lens.defaultRoots else cli.roots
  let cfg : Lens.Config := { pkg := cli.pkg }
  match ← Lens.runPipeline cli.module roots cfg with
  | .error errs =>
    Lens.reportErrors errs
    return 1
  | .ok text =>
    match cli.out with
    | none =>
      IO.println text
      return 0
    | some outDir =>
      let dir : System.FilePath := outDir
      IO.FS.createDirAll dir
      clearScalaFiles dir
      let file := dir / "Shallot.scala"
      IO.FS.writeFile file text
      IO.println s!"lens: wrote {file} ({(text.splitOn "\n").length} lines, roots: {roots.length})"
      return 0
