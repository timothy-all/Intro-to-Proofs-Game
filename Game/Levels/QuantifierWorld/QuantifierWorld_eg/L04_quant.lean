import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L03_quant

World "QuantifierWorld_eg"
Level 4

Title "Example 4"

Introduction "
## **Level 4**
"

Statement {u : Type*} (P R S : u → Prop) (h1 : ∀ x, P (x) → R (x)) (h2 : ∀ x, P (x) ∧ S (x) ) : ∀ x, R (x) ∧ S (x) := by
  intro a
  obtain hPS := h2 a
  obtain hR := h1 a hPS.left
  exact And.intro hR hPS.right

Conclusion ""
