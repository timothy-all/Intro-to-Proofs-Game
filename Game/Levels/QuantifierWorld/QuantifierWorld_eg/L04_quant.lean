import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L03_quant

World "QuantifierWorld_eg"
Level 4

Title "Example 4"

Introduction "
## **Level 4**

"


Statement {u : Type} (P Q : u → Prop) (h: ∀ x, P x ∧ Q x) : (∀ x, P x) := by
  intro x
  exact (h x).left



Conclusion ""
