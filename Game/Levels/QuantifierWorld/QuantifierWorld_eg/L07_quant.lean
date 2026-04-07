import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L06_quant

World "QuantifierWorld_eg"
Level 7

Title "Example 7"

Introduction "
## **Level 7**

"


Statement {u : Type} (P : u → u → Prop) : (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
  intro h y x
  exact h x y

Conclusion ""
