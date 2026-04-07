import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L05_quant

World "QuantifierWorld_eg"
Level 6

Title "Example 6"

Introduction "
## **Level 6**

"


Statement {u : Type} (P Q : u → Prop) : ((∃ x, P x) ∨ (∃ x, Q x)) ↔ ∃ x, P x ∨ Q x := by
  constructor
  intro h
  obtain ⟨x,hx⟩ | ⟨y,hy⟩ := h
  use x
  left
  exact hx
  use y
  right
  exact hy
  intro ⟨x,h⟩
  obtain hP | hQ := h
  left
  use x
  right
  use x


Conclusion ""
