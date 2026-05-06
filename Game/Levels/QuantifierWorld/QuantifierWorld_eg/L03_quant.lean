import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L02_quant

World "QuantifierWorld_eg"
Level 3

Title "Example 3"

Introduction "
## **Level 3**

"


Statement {u : Type} (P Q R : u → Prop) (h1 : (∀ x, P x) → (∃ y, Q y)) (h2 : ∀ y, ¬ Q y) (h3 : ∀ x, ¬ P x → R x) : ∃ x, R x := by
  rw[Contrapositive] at h1
  push_neg at h1 -- needs introduced
  obtain ⟨x,hx⟩ := h1 h2
  use x
  exact h3 x hx


Conclusion ""
