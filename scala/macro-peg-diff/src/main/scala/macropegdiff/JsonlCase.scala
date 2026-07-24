package macropegdiff

/** One line of the differential harness's canonical JSONL output, matching
  * `lean/CounterexampleRunner.lean`'s `ceJsonlLine` and
  * `lean/MacroPeg/CounterexampleCorpus.lean`'s `ceCases` ids exactly, so a
  * byte-for-byte diff against the Lean side's output is possible.
  */
final case class JsonlCase(caseId: String, result: String, phase: String = "eval", status: String = "ok"):
  def toJsonLine: String =
    s"""{"case":"$caseId","phase":"$phase","status":"$status","result":"$result"}"""
