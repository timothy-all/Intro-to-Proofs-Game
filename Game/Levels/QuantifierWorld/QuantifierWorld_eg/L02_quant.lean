import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L01_quant

World "QuantifierWorld_eg"
Level 2

Title "Example 2"

Introduction "
## **Level 2**
"

Statement {u : Type*} {P Q : u → Prop} (h : (∃ x, P x) ∧ (∃ x, Q x) ) : ∃ x, P x ∨ Q x := by
  obtain ⟨ ⟨x,hx⟩, ⟨y,hy⟩⟩ := h
  exist x
  left
  exact hx

Conclusion ""
