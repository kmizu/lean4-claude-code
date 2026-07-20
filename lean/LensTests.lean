/-!
# Lens test driver (M0 stub)

Golden tests land in M1: extract `LensTest/Corpus/*.lean` roots, diff the
pretty-printed Scala against `tests/golden/*.scala`.
-/

def main : IO UInt32 := do
  IO.println "lenstests: 0 tests (golden suite lands in M1)"
  return 0
