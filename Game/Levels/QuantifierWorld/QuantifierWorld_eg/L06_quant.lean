import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L05_quant

World "QuantifierWorld_eg"
Level 6

Title "Example 6"

Introduction "
# **Level 6**
Just another practice problem.
"


Statement {u : Type} (P Q : u → Prop) (h1 : ∃ x, P x) (h2 : ∀ x, ¬ Q x) : ∃ x, P x ∨ Q x := by
  obtain ⟨x,hx⟩ := h1
  exist x
  left
  exact hx

Conclusion ""


/- Save for pf strategy with or statements
Statement {u : Type} (P Q : u → Prop) (h : ((∃ x, P x) ∨ (∃ x, Q x))): ∃ x, P x ∨ Q x := by-/
