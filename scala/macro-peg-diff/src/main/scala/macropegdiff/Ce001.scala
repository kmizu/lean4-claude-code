package macropegdiff

import com.github.kmizu.macro_peg.{Ast, Evaluator, EvaluationStrategy}
import com.github.kmizu.macro_peg.GrammarDsl.*

/** CE-001: evaluation-strategy non-equivalence.
  *
  * Surface grammar (`lean/MacroPeg/Counterexamples.lean`'s
  * `strategyDivergeGrammar`, transcribed here in the reference's own
  * `Ast.Grammar` shape via `GrammarDsl`):
  *
  * {{{
  * S = F("a") !.;
  * F(x) = "b";   // F never references its parameter x
  * }}}
  *
  * Input `"ab"`. Independent oracle: the reference's own 3 evaluation
  * strategies cross-check each other (`CallByValueSeq` disagrees with
  * `CallByName`/`CallByValuePar`, which happen to coincide here) — ground
  * truth re-verified against the live reference via `sbt console` this
  * session: CallByName -> Failure, CallByValueSeq -> Success(""),
  * CallByValuePar -> Failure.
  */
object Ce001:
  val ce001Grammar: Ast.Grammar = grammar(
    rule("S", call("F", str("a")) ~ notP(wild)),
    ruleHO("F", str("b"), "x")
  )

  val input: String = "ab"

  def outcomeFor(strategy: EvaluationStrategy): Outcome =
    Outcome.ofEvaluationResult(Evaluator(ce001Grammar, strategy).evaluate(input, Symbol("S")))

  def cases: List[JsonlCase] = List(
    JsonlCase("500-ce001-strategy-name-ab", Outcome.render(outcomeFor(EvaluationStrategy.CallByName))),
    JsonlCase("501-ce001-strategy-seq-ab", Outcome.render(outcomeFor(EvaluationStrategy.CallByValueSeq))),
    JsonlCase("502-ce001-strategy-par-ab", Outcome.render(outcomeFor(EvaluationStrategy.CallByValuePar)))
  )
