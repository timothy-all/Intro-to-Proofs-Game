import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L01_quant

World "QuantifierWorld_eg"
Level 2

Title "Example 2"

Introduction "
## **Level 2**
"

Statement {u : Type*} {P Q : u → Prop} (h: (∀ x, P x) ∧ (∀ x, Q x)) : ∀ x, P x ∧ Q x := by
  intro x
  exact And.intro (h.left x) (h.right x)

Conclusion "The converse of this is also true."
