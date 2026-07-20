/-!
# shallot-runner (M0 stub)

Differential-harness Lean side: reads corpus programs and emits canonical
JSONL (`case`/`phase`/`status`/`result`). Real implementation lands in M2
together with `Shallot.Render`.
-/

def main (_args : List String) : IO UInt32 := do
  IO.println "shallot-runner: stub (corpus harness lands in M2)"
  return 0
