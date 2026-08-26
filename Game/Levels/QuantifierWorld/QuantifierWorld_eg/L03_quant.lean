import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L02_quant

World "QuantifierWorld_eg"
Level 3

Title "Example 3"

Introduction "
## **Level 3**
"



Statement {u : Type*} (P : u → u → Prop) : (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
  intro h y x
  exact h x y


Conclusion ""


NewTheorem Forall_and
