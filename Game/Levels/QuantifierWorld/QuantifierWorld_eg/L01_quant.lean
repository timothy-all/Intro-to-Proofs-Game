import Game.Levels.QuantifierWorld

World "QuantifierWorld_eg"
Level 1

Title "Example 1"

Introduction "
## **Level 1**

"


Statement (u : Type) (P Q R S : u → Prop) (h1 : ∀ x, P (x) → (Q (x) ∧ R (x))) (h2 : ∀ x, P (x) ∧ S (x) ) : ∀ x, R (x) ∧ S (x) := by
  intro a
  obtain hPS := h2 a
  obtain hRQ := h1 a hPS.left
  exact And.intro hRQ.right hPS.right



Conclusion ""
