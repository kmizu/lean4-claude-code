package shallot.cli

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets

object Main:
  /** Differential harness, Scala side: evaluate the EXTRACTED case table
    * (`shallot.gen.cases`) and emit the same canonical JSONL as the Lean
    * runner. Key order and formatting must match `lean/Runner.lean`.
    */
  def dumpJsonl: String =
    // Deep-recursion corpus cases (07x) need a big stack; the extracted
    // interpreter is fuel-bounded, non-tail structural recursion.
    shallot.rt.Stack.run(256) {
      val lines = shallot.gen.cases.map { case (id, result) =>
        s"""{"case":"$id","phase":"eval","status":"ok","result":"$result"}"""
      }
      lines.mkString("", "\n", "\n")
    }

  def main(args: Array[String]): Unit =
    args.toList match
      case "version" :: _ =>
        println("shallot-cli 0.1.0 (M2)")
      case "dump" :: out :: _ =>
        Files.write(Paths.get(out), dumpJsonl.getBytes(StandardCharsets.UTF_8))
        System.err.println(s"shallot-cli: wrote $out")
      case "dump" :: Nil =>
        print(dumpJsonl)
      case _ =>
        println("usage: shallot-cli <version|dump [outfile]> (run/typecheck/compile land in M7+)")
