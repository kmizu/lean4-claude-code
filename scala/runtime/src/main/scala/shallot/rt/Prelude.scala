package shallot.rt

/** Hand-written runtime prelude for Lens-extracted code.
  *
  * Part of the TCB: Lean's `Nat`/`Int` map to `BigInt` with Lean's exact
  * semantics — truncated `Nat` subtraction, division/modulo by zero = 0.
  * The `Int` division/modulo flavor (T- vs E-division) is pinned empirically
  * against `#eval` tables in M1 (corpus 00x) before any `Int` div/mod mapping
  * is added here.
  */
object Prelude:
  def natSub(a: BigInt, b: BigInt): BigInt = (a - b).max(0)
  def natDiv(a: BigInt, b: BigInt): BigInt = if b == 0 then 0 else a / b
  def natMod(a: BigInt, b: BigInt): BigInt = if b == 0 then a else a % b

  final case class LensPanic(msg: String) extends RuntimeException(msg)
  def panic[A](msg: String): A = throw LensPanic(msg)

object Stack:
  /** Run `f` on a fresh thread with an explicit stack size in MB.
    *
    * Extracted code is fuel-bounded, non-tail structural recursion; deep
    * inputs need deep stacks even when the JVM was launched with defaults.
    */
  def run[A](sizeMB: Int)(f: => A): A =
    var result: Either[Throwable, A] = Left(IllegalStateException("shallot-deep-stack thread did not run"))
    val t = Thread(
      null,
      () => result = try Right(f) catch { case e: Throwable => Left(e) },
      "shallot-deep-stack",
      sizeMB.toLong * 1024 * 1024
    )
    t.start()
    t.join()
    result match
      case Right(a) => a
      case Left(e)  => throw e
