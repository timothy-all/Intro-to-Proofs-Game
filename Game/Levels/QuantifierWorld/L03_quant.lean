import Game.Levels.QuantifierWorld.L02_quant

World "QuantifierWorld"
Level 3

Title "Existential Quantifiers"

Introduction "
## **Level 3**

"


Statement {u : Type} (a : u) (P : u → Prop) (h : P a) : ∃ x, P x := by
  use a

Conclusion ""

NewTactic use
