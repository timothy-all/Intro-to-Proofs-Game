import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L01_quant

World "QuantifierWorld_eg"
Level 2

Title "Example 2"

Introduction "
# **Level 2**
This level ought to give you practice with an existentially quantified goal.
"

/-- How can one view the statement below as a glorified combination of `Or_and_left` and `And_or_left`? -/
Statement {u : Type*} {P Q : u → Prop} (h : (∃ x, P x) ∧ (∃ x, Q x) ) : ∃ x, P x ∨ Q x := by
  obtain ⟨ ⟨x,hx⟩, ⟨y,hy⟩⟩ := h
  exist x
  left
  exact hx

Conclusion "🤔 Is this statement still true if we replace the original goal with `∃ x, P x ∧ Q x`? No! Why? Think of a counter-example."
