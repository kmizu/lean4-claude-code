package macropegdiff

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

/** Independent differential driver, counterexample side: runs CE-001 and
  * CE-002 against the vendored LIVE reference `Evaluator`
  * (`scala/macro-peg-ref/`) and emits the same canonical JSONL shape as
  * `lean/CounterexampleRunner.lean`, for a byte-for-byte diff against that
  * Lean runner's own output (see `scripts/counterexample-diff.sh`).
  * CE-003 has no Lean-side counterpart (see `Ce003`'s module doc) and is
  * instead reported as a human-readable PASS/FAIL verdict on stderr.
  *
  * Usage mirrors `shallot-cli`'s `macro-dump` subcommand, but as its own
  * main class in this separate `macroPegDiff` sbt project:
  *
  * {{{
  * sbt macroPegDiff/run              // JSONL (CE-001+CE-002) to stdout
  * sbt "macroPegDiff/run out.jsonl"  // JSONL (CE-001+CE-002) to out.jsonl
  * }}}
  *
  * The CE-003 report is ALWAYS printed to stderr, regardless of the CLI
  * argument, since it has no JSONL representation to redirect.
  */
object Main:
  def jsonl: String =
    (Ce001.cases ++ Ce002.cases).map(_.toJsonLine).mkString("", "\n", "\n")

  def main(args: Array[String]): Unit =
    args.toList match
      case out :: _ =>
        Files.write(Paths.get(out), jsonl.getBytes(StandardCharsets.UTF_8))
        System.err.println(s"macro-peg-diff: wrote $out")
      case Nil =>
        print(jsonl)

    System.err.println(s"macro-peg-diff: CE-002 ce002Grammar.isWellFormed = ${Ce002.isWellFormed} (expected true -- the well-formedness checker's blind spot IS the counterexample)")
    System.err.println()
    System.err.print(Ce003.report())
