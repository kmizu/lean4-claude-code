package macropegdiff

import com.github.kmizu.macro_peg.EvaluationResult

/** Mirrors the Lean side's 3-constructor `CmpOutcome`
  * (`lean/MacroPeg/Outcome.lean`): `accept rest` / `reject` / `diverge`.
  * Deliberately only 3 constructors — no 4th "runtime error" case, matching
  * the Lean side exactly, since `EvaluationResult` itself only ever
  * distinguishes success/failure (this module's `diverge` is produced by
  * [[Ce002]]'s own timeout wrapper, never by [[EvaluationResult]] directly).
  */
enum Outcome:
  case Accept(rest: String)
  case Reject
  case Diverge

object Outcome:
  /** `EvaluationResult` only ever carries success/failure — never diverge,
    * exactly like `CmpOutcome.ofMOutcome` on the Lean side.
    */
  def ofEvaluationResult(result: EvaluationResult): Outcome = result match
    case EvaluationResult.Success(rest) => Outcome.Accept(rest)
    case EvaluationResult.Failure => Outcome.Reject

  /** Reimplements `lean/MacroPeg/Render.lean`'s `renderMPeg` convention by
    * hand: `"fail"` for a failure, `"ok+N"` for success with `N` characters
    * remaining, `"fuel"` for diverge/gave-up. Deliberately NOT shared code
    * with the Lean-extracted renderer — the whole point of this module is
    * to be an independent oracle.
    */
  def render(outcome: Outcome): String = outcome match
    case Outcome.Accept(rest) => s"ok+${rest.length}"
    case Outcome.Reject => "fail"
    case Outcome.Diverge => "fuel"
