package macropegdiff

import com.github.kmizu.macro_peg.{Ast, Evaluator, EvaluationStrategy}
import com.github.kmizu.macro_peg.GrammarDsl.*

import java.util.concurrent.{Executors, ThreadFactory, TimeoutException}
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.*

/** CE-002: well-formedness does NOT imply termination.
  *
  * Surface grammar (`lean/MacroPeg/Divergence.lean`'s `selfCallGrammar`,
  * transcribed here in the reference's own `Ast.Grammar` shape):
  *
  * {{{
  * S = F(S) !.;
  * F(x) = x;
  * }}}
  *
  * `ce002Grammar.isWellFormed` returns `true` — the reference's own
  * `leadsToSelf` left-recursion check (`Ast.scala`/`GrammarValidator.scala`)
  * only compares rule names / formal parameter names syntactically and
  * never traces what actual argument expression got substituted in for a
  * callee's formal parameter, so it never notices that `F(S)`'s parameter
  * `x`, once substituted with the actual argument `S`, makes evaluating `S`
  * loop back into evaluating `S` again.
  *
  * Evaluating `S` under `CallByName` on any input diverges: infinite
  * mutual recursion between `Evaluator`'s private `evaluateIn` and
  * `evaluateWithoutMemo`, confirmed this session via a 5-second-timeout
  * `Future` against the live reference. It does NOT throw an exception —
  * it just runs forever. We run it on a dedicated large-stack daemon
  * thread and bound it with `Await.result`'s timeout; on timeout we
  * abandon the still-running background thread (a daemon thread, so it
  * cannot block JVM shutdown) rather than trying to interrupt CPU-bound
  * mutual recursion, which is out of scope and not reliably possible
  * anyway. A `StackOverflowError` (Scala's `Future` treats it as
  * non-fatal and would otherwise surface as a failed `Future`) is treated
  * identically to a timeout: either way we "gave up", which is exactly
  * what the shared `fuel` rendering convention means.
  */
object Ce002:
  val ce002Grammar: Ast.Grammar = grammar(
    rule("S", call("F", ref("S")) ~ notP(wild)),
    ruleHO("F", ref("x"), "x")
  )

  /** Any input diverges; empty matches the Lean side's `selfCallGrammar`
    * check (`CounterexampleCorpus.lean`'s `ceCase002` also uses `[]`).
    */
  val input: String = ""

  def isWellFormed: Boolean = ce002Grammar.isWellFormed

  /** A dedicated single-thread executor with a large stack, so the
    * infinite mutual recursion has room to genuinely "run forever" within
    * our observation window instead of hitting a stack limit within
    * milliseconds. The thread is a daemon so an abandoned run-forever task
    * never blocks JVM exit. In practice, when a `StackOverflowError`
    * eventually does occur deep in this mutual recursion, it tends to
    * happen with so little stack margin left that even `Future`'s own
    * `NonFatal` catch can't complete the promise -- the error escapes to
    * this thread's uncaught-exception handler instead of surfacing as a
    * failed `Future`. That's expected and harmless (we just fall through
    * to `Await.result`'s `TimeoutException` instead), but the JVM's
    * default handler would otherwise dump a very long, noisy stack trace
    * to stderr for a condition we already handle correctly -- so it's
    * silenced here.
    */
  private def bigStackExecutionContext(): ExecutionContext =
    val threadFactory: ThreadFactory = (r: Runnable) =>
      val t = new Thread(null, r, "ce002-diverge-probe", 256L * 1024 * 1024)
      t.setDaemon(true)
      t.setUncaughtExceptionHandler((_, _) => ())
      t
    ExecutionContext.fromExecutor(Executors.newSingleThreadExecutor(threadFactory))

  def checkDiverges(timeout: FiniteDuration = 3.seconds): Outcome =
    given ExecutionContext = bigStackExecutionContext()
    val probe = Future(Evaluator(ce002Grammar, EvaluationStrategy.CallByName).evaluate(input, Symbol("S")))
    try Outcome.ofEvaluationResult(Await.result(probe, timeout))
    catch
      case _: TimeoutException => Outcome.Diverge
      case _: StackOverflowError => Outcome.Diverge

  def cases: List[JsonlCase] = List(
    JsonlCase("510-ce002-selfcall-diverges", Outcome.render(checkDiverges()))
  )
