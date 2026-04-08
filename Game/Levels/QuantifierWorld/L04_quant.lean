import Game.Levels.QuantifierWorld.L03_quant

World "QuantifierWorld"
Level 4

Title "Universal Quantifiers"

Introduction "
## **Level 4**

"


Statement {u : Type} (P Q : u → Prop) (h₁ : ∀ x, P x → Q x) (h₂ : ∃ x, P x) : ∃ x, Q x := by
  obtain ⟨a,ha⟩ := h₂
  use a
  exact h₁ a ha

Conclusion ""
