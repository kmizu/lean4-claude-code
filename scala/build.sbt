ThisBuild / scalaVersion := "3.7.4"
ThisBuild / organization := "com.github.kmizu.shallot"

val munitV = "1.1.1"
val munitScalacheckV = "1.1.0"

val strictOpts = Seq("-deprecation", "-feature", "-Wunused:all", "-Werror")

lazy val commonTestSettings = Seq(
  libraryDependencies ++= Seq(
    "org.scalameta" %% "munit" % munitV % Test,
    "org.scalameta" %% "munit-scalacheck" % munitScalacheckV % Test
  ),
  Test / fork := true,
  Test / javaOptions ++= Seq("-Xss512m", "-Xmx2g")
)

// Hand-written runtime prelude for extracted code (part of the TCB).
lazy val runtime = project
  .in(file("runtime"))
  .settings(
    name := "shallot-runtime",
    scalacOptions ++= strictOpts,
    commonTestSettings
  )

// Extractor output. Lax flags: generated code is exempt from lint policy;
// its correctness is covered by the differential harness.
lazy val generated = project
  .in(file("generated"))
  .dependsOn(runtime)
  .settings(
    name := "shallot-generated",
    scalacOptions ++= Seq("-deprecation"),
    Compile / doc / sources := Nil
  )

// Hand-written demo CLI; `dump` doubles as the differential harness's Scala side.
lazy val shallotCli = project
  .in(file("shallot-cli"))
  .dependsOn(generated)
  .settings(
    name := "shallot-cli",
    scalacOptions ++= strictOpts,
    commonTestSettings
  )

// Vendored reference implementation (kmizu/macro_peg, frozen commit -- see
// UPSTREAM.md). Lax flags: vendored code is exempt from this repo's lint policy.
lazy val macroPegRef = project
  .in(file("macro-peg-ref"))
  .settings(
    name := "macro-peg-ref",
    scalacOptions ++= Seq("-deprecation"),
    Compile / doc / sources := Nil
  )

// Independent differential driver for the 3 hand-picked counterexamples
// (CE-001/002/003) against the vendored reference `Evaluator`. Hand-written
// code authored for this project: strict lint settings apply (unlike the
// vendored macroPegRef it depends on).
lazy val macroPegDiff = project
  .in(file("macro-peg-diff"))
  .dependsOn(macroPegRef)
  .settings(
    name := "macro-peg-diff",
    scalacOptions ++= strictOpts,
    commonTestSettings
  )

lazy val root = project
  .in(file("."))
  .aggregate(runtime, generated, shallotCli, macroPegRef, macroPegDiff)
  .settings(
    name := "shallot-root",
    publish / skip := true
  )
