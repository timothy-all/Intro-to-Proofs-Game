import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L01_quant
import Mathlib.Tactic.Use

World "QuantifierWorld_eg"
Level 2

Title "Example 2"

Introduction "
## **Level 2**

"


Statement {u : Type} (P Q: u → Prop) (h1: ∃ x, P x) (h2 : ∀ x, Q x) : ∃ x, P x ∧ Q x := by
  obtain ⟨w,h⟩ := h1
  use w
  obtain hQ := h2 w
  exact And.intro h hQ

Conclusion ""
