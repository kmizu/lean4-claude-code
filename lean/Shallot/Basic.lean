/-!
# Shallot — M0 stub

Placeholder content so the whole pipeline (lake build → extraction → sbt)
can be wired end-to-end before the real language arrives in M2.
-/

namespace Shallot

/-- M0 pipeline stub inductive; replaced by the real AST in M2. -/
inductive Color where
  | red
  | green
  | blue

def Color.describe : Color → String
  | .red => "red"
  | .green => "green"
  | .blue => "blue"

def hello : String := "shallot"

theorem hello_length : hello.length = 7 := rfl

end Shallot
