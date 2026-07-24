package macropegdiff

import com.github.kmizu.macro_peg.{Ast, Evaluator, EvaluationStrategy, MacroExpander}
import com.github.kmizu.macro_peg.GrammarDsl.*

/** CE-003: `MacroExpander` capture bug (non-hygienic substitution).
  *
  * Surface grammar, three rules:
  *
  * {{{
  * Id(x) = (x -> x x);
  * Apply(f) = f("z");
  * S = Apply(Id("q")) !.;
  * }}}
  *
  * Correct/hygienic behavior would have `S` accept `"zz"` (`Apply` calls
  * the closure with `"z"`, the closure matches `"z"` twice) and reject
  * `"qq"`/`"q"`. The reference's actual (buggy) behavior:
  * `MacroExpander.expandGrammar`'s non-hygienic `substitute` incorrectly
  * substitutes `Id`'s own parameter `x = q` into the INNER lambda's body
  * too (which should have been shielded by the lambda's own `x` parameter
  * shadowing it) — so `S`'s fully-expanded body collapses to the fixed
  * expression matching literal `q` then literal `q` then end of input,
  * completely losing the connection to `Apply`'s real argument `z`.
  *
  * Independent oracle: NONE. Unlike CE-001 (where the reference's own 3
  * evaluation strategies cross-check each other), there is no second
  * implementation to run for this one — `Shallot.MacroPeg`'s own `MExp` is
  * de Bruijn indexed, so it has no bound-variable NAMES to shadow/capture
  * in the first place (see `lean/MacroPeg/Counterexamples.lean`'s module
  * docstring). The oracle here is simply the hardcoded
  * expected-if-hygienic-vs-actual table below, transcribed from ground
  * truth re-verified against the live reference via `sbt console` this
  * session: input `"qq"` -> Success, input `"q"` -> Failure, input `"zz"`
  * -> Failure (this is the key evidence the bug is real: a correctly
  * hygienic implementation would accept `"zz"`, not `"qq"`).
  */
object Ce003:
  val ce003Grammar: Ast.Grammar = grammar(
    ruleHO("Id", fn("x")(ref("x") ~ ref("x")), "x"),
    ruleHO("Apply", call("f", str("z")), "f"),
    rule("S", call("Apply", call("Id", str("q"))) ~ notP(wild))
  )

  val expandedGrammar: Ast.Grammar = MacroExpander.expandGrammar(ce003Grammar)

  def evaluate(input: String): Outcome =
    Outcome.ofEvaluationResult(
      Evaluator(expandedGrammar, EvaluationStrategy.CallByName).evaluate(input, Symbol("S"))
    )

  /** One probed input, paired with what a hygienic implementation would
    * produce versus what the live (buggy) reference actually produces.
    */
  final case class Trial(input: String, expectedIfHygienic: Outcome, actual: Outcome)

  def trials: List[Trial] = List(
    Trial("qq", Outcome.Reject, evaluate("qq")),
    Trial("q", Outcome.Reject, evaluate("q")),
    Trial("zz", Outcome.Accept(""), evaluate("zz"))
  )

  /** PASS means: we successfully reproduced the documented capture bug —
    * i.e. the reference's actual behavior matches the BUGGY table
    * (`"qq"` accepts, `"q"` rejects, `"zz"` rejects), not the hygienic one.
    */
  def reproducesBug: Boolean =
    evaluate("qq") == Outcome.Accept("") &&
      evaluate("q") == Outcome.Reject &&
      evaluate("zz") == Outcome.Reject

  /** Human-readable report for stderr — this counterexample has no
    * Lean-side JSONL counterpart, so there is nothing to golden-compare.
    */
  def report(): String =
    val sb = new StringBuilder
    sb.append("CE-003: MacroExpander capture bug (non-hygienic substitution)\n")
    sb.append("  grammar: Id(x) = (x -> x x); Apply(f) = f(\"z\"); S = Apply(Id(\"q\")) !.;\n")
    sb.append("  independent oracle: NONE (MExp is de Bruijn indexed; see module doc) -- hardcoded expected-vs-actual only\n")
    for trial <- trials do
      val expected = Outcome.render(trial.expectedIfHygienic)
      val actual = Outcome.render(trial.actual)
      sb.append(f"""  input="${trial.input}%-3s" expected-if-hygienic=$expected%-6s actual=$actual%-6s${if expected == actual then " (matches hygienic!)" else " (matches BUGGY reference)"}\n""")
    val verdict = if reproducesBug then "PASS" else "FAIL"
    sb.append(s"  verdict: $verdict (did-we-reproduce-the-documented-capture-bug)\n")
    sb.toString
