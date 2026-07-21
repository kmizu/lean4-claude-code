package shallot.cli

import java.nio.file.{Files, Paths}
import java.nio.charset.{StandardCharsets, CodingErrorAction, CharacterCodingException}
import java.nio.ByteBuffer
import scala.jdk.CollectionConverters.*

/** JSONTestSuite runner, Scala side — the EXTRACTED verified parser over
  * the same vendored corpus as `lake exe json-suite`, same verdict format,
  * same strict-UTF-8 convention (malformed bytes = `reject:invalid-utf8`).
  */
object JsonSuite:
  private def decodeStrict(bytes: Array[Byte]): String =
    StandardCharsets.UTF_8.newDecoder()
      .onMalformedInput(CodingErrorAction.REPORT)
      .onUnmappableCharacter(CodingErrorAction.REPORT)
      .decode(ByteBuffer.wrap(bytes))
      .toString

  private def verdict(bytes: Array[Byte]): String =
    try
      val s = decodeStrict(bytes)
      shallot.gen.Json_parseJson(BigInt(10000000), s) match
        case Right(_) => "accept"
        case Left(e)  => "reject:" + shallot.gen.Json_JErr_render(e)
    catch case _: CharacterCodingException => "reject:invalid-utf8"

  def run(dir: String): String =
    shallot.rt.Stack.run(256) {
      val files = Files.list(Paths.get(dir)).iterator().asScala
        .filter(_.getFileName.toString.endsWith(".json"))
        .toList.sortBy(_.getFileName.toString)
      val lines = files.map { p =>
        s"""{"file":"${p.getFileName}","verdict":"${verdict(Files.readAllBytes(p))}"}"""
      }
      lines.mkString("", "\n", "\n")
    }
