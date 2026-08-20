import Game.Levels.QuantifierWorld.L04_quant
import Mathlib.Tactic.Push

World "QuantifierWorld"
Level 5

Title "Universal Quantifiers"

Introduction "
## **Level 5**

"

Statement {u : Type} (P : u → Prop) (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  push_neg at h
  exact h

Conclusion ""

NewTactic push_neg
