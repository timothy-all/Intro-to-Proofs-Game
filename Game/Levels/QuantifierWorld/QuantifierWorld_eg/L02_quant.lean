import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L01_quant

World "QuantifierWorld_eg"
Level 2

Title "Example 2"

Introduction "
## **Level 2**

"


Statement {u : Type} (P Q: u → Prop) (h1: ∃ x, P x) (h2 : ∀ x, Q x) : ∃ x, P x ∧ Q x := by
  rcases h1 with ⟨a,hP⟩ -- anyway to avoid this? seems too early
  use a
  obtain hQ := h2 a
  exact And.intro hP hQ

Conclusion ""
