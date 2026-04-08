import Game.Levels.QuantifierWorld.L01_quant

World "QuantifierWorld"
Level 2

Title "Universal Quantifiers"

Introduction "
## **Level 1**

"


Statement {u : Type} (a : u) (P Q : u → Prop) (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  exact h1 x (h2 x)

Conclusion ""
