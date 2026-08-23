import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L04_quant

World "QuantifierWorld_eg"
Level 5

Title "Example 5"

Introduction "
## **Level 5**
"

Statement {u : Type*} (P : u → u → Prop) : (∃ x,∃ y, P x y) → (∃ y, ∃ x, P x y) := by
  intro ⟨x,y,hP⟩
  use y
  use x
  exact hP

Conclusion ""
