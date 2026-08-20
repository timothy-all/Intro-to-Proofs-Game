import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L04_quant

World "QuantifierWorld_eg"
Level 5

Title "Example 5"

Introduction "
## **Level 5**

"


Statement {u : Type*} {P Q : u → Prop} (h: (∀ x, P x) ∧ (∀ x, Q x)) : ∀ x, P x ∧ Q x := by
  intro x
  exact And.intro (h.left x) (h.right x)


Conclusion "The converse is also true. We unlock this theorem from here on out."
