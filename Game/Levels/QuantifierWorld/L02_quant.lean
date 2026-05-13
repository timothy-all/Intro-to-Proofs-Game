import Game.Levels.QuantifierWorld.L01_quant

World "QuantifierWorld"
Level 2

Title "Universal Quantifiers"

Introduction "
## **Level 2**

"


Statement {u : Type} (a : u) (P Q : u → Prop) (hPQ : ∀ x, P x → Q x) (hP : ∀ x, P x) : ∀ x, Q x := by
  intro x
  exact hPQ x (hP x)

Conclusion ""
