package shallot.cli

object Main:
  def main(args: Array[String]): Unit =
    args.toList match
      case "version" :: _ =>
        println("shallot-cli 0.1.0 (M0 stub)")
      case _ =>
        println("usage: shallot-cli <version|run|typecheck|compile|dump> ... (subcommands land in M2+)")
