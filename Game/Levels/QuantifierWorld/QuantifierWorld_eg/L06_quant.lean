import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L05_quant

World "QuantifierWorld_eg"
Level 6

Title "Example 6"

Introduction "
## **Level 6**

"

theorem Forall_and.{u_1} {v : Sort u_1} {P Q : v → Prop} : (∀ (x : v), P (x : v) ∧ Q x) ↔ ((∀ (x : v), P x) ∧ (∀ (x : v), Q x)) := by
  rw[forall_and]


Statement {u : Type} (P Q : u → Prop) (h₁ : ∃ x, P x) (h₂ : ∀ x, ¬ Q x) : ∃ x, P x ∨ Q x := by
  obtain ⟨x,hx⟩ := h₁
  use x
  left
  exact hx

Conclusion ""

NewTactic left right
NewTheorem Forall_and

/- Save for pf strategy with or statements
Statement {u : Type} (P Q : u → Prop) (h : ((∃ x, P x) ∨ (∃ x, Q x))): ∃ x, P x ∨ Q x := by-/
