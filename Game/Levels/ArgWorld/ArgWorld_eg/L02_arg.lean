import Game.Levels.ArgWorld.ArgWorld_eg.L01_arg

World "ArgWorld"
Level 6

Title "Conditional Proof"

Introduction "
### **Level 6**
"


Statement (P Q R: Prop) (h1 : P ∧ Q) (h2 : P → (Q → R)) : R := by
  rw[← curry] at h2
  exact h2 h1

Conclusion ""
