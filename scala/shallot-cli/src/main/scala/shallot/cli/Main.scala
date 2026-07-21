package shallot.cli

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets

/** The Shallot CLI — every language operation below runs through code
  * EXTRACTED from Lean (parser = the formally verified PEG interpreter,
  * typechecker = proven sound+complete, interpreter = proven type-sound,
  * VM = proven equivalent to the interpreter).
  */
object Main:
  private def readSource(path: String): String =
    new String(Files.readAllBytes(Paths.get(path)), StandardCharsets.UTF_8)

  /** Differential harness, Scala side: evaluate the EXTRACTED case table
    * and emit the same canonical JSONL as the Lean runner (Runner.lean).
    */
  def dumpJsonl: String =
    shallot.rt.Stack.run(256) {
      val lines = shallot.gen.cases.map { case (id, result) =>
        s"""{"case":"$id","phase":"eval","status":"ok","result":"$result"}"""
      }
      lines.mkString("", "\n", "\n")
    }

  def main(args: Array[String]): Unit =
    args.toList match
      case "version" :: _ =>
        println("shallot-cli 1.0.0 (all language operations are Lean-extracted)")
      case "run" :: path :: _ =>
        println(shallot.rt.Stack.run(256) { shallot.gen.runSource(readSource(path)) })
      case "eval" :: src :: _ =>
        println(shallot.rt.Stack.run(256) { shallot.gen.runSource(src) })
      case "json" :: src :: _ =>
        println(shallot.rt.Stack.run(64) {
          shallot.gen.Json_parseJson(BigInt(10000000), src) match
            case Right(v) => "ok:" + shallot.gen.Json_printJson(v)
            case Left(e)  => "err:" + shallot.gen.Json_JErr_render(e)
        })
      case "json-suite" :: dir :: rest =>
        val out = JsonSuite.run(dir)
        rest match
          case o :: _ =>
            Files.write(Paths.get(o), out.getBytes(StandardCharsets.UTF_8))
            System.err.println(s"shallot-cli: wrote $o")
          case Nil => print(out)
      case "dump" :: out :: _ =>
        Files.write(Paths.get(out), dumpJsonl.getBytes(StandardCharsets.UTF_8))
        System.err.println(s"shallot-cli: wrote $out")
      case "dump" :: Nil =>
        print(dumpJsonl)
      case _ =>
        println("""usage: shallot-cli <command>
          |  run <file>    parse (verified PEG), typecheck, evaluate a .shl file
          |  eval <src>    same, on a source string argument
          |  dump [file]   differential-harness JSONL (extracted case table)
          |  version""".stripMargin)
