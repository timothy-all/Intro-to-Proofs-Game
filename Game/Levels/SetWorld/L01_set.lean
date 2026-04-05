import Game.Levels.QuantifierWorld

World "SetWorld"
Level 1

Title "name"

Introduction "
## **Level 1**

"


Statement {u : Type} (A B : Set u) (h : A ⊆ B) : ∀ x, x ∈ A → x ∈ B := by
  exact h


Conclusion ""
