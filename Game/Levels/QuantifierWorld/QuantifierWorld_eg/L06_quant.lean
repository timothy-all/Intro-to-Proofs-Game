import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L05_quant

World "QuantifierWorld_eg"
Level 6

Title "Example 6"

Introduction "
## **Level 6**
"



Statement {u : Type} (P Q : u → Prop) (h₁ : ∃ x, P x) (h₂ : ∀ x, ¬ Q x) : ∃ x, P x ∨ Q x := by
  obtain ⟨x,hx⟩ := h₁
  exist x
  left
  exact hx

Conclusion ""


/- Save for pf strategy with or statements
Statement {u : Type} (P Q : u → Prop) (h : ((∃ x, P x) ∨ (∃ x, Q x))): ∃ x, P x ∨ Q x := by-/
