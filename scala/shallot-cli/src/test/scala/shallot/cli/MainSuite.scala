package shallot.cli

class MainSuite extends munit.FunSuite:
  test("version subcommand runs"):
    Main.main(Array("version"))
