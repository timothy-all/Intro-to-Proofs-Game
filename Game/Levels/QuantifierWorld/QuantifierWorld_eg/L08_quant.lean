import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L07_quant

World "QuantifierWorld_eg"
Level 8

Title "Example 8"

Introduction "
## **Level 8**

"


Statement {u : Type} (P : u → u → Prop) : (∃ x,∃ y, P x y) → (∃ y, ∃ x, P x y) := by
  intro ⟨x,y,hP⟩
  use y,x

Conclusion ""
