import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L07_quant

World "QuantifierWorld_eg"
Level 8

Title "Example 8"

Introduction "
## **Level 8**
"

Statement {u : Type} (P Q R : u → Prop) (h1 : (∀ x, P x) → (∃ y, Q y)) (h2 : ∀ y, ¬ Q y) (h3 : ∀ x, ¬ P x → R x) : ∃ x, R x := by
  rw[Contrapositive] at h1
  rw[Not_forall,Not_exists] at h1
  obtain ⟨x,hx⟩ := h1 h2
  exist x
  exact h3 x hx

Conclusion ""
