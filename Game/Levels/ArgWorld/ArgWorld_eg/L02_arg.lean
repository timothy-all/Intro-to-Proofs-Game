import Game.Levels.ArgWorld.ArgWorld_eg.L01_arg

World "ArgWorld_eg"
Level 2

Title "Conditional Proof"

Introduction "
### **Level 2**
"


Statement (P Q R: Prop) (h1 : P ∧ Q) (h2 : P → (Q → R)) : R := by
  rw[← curry] at h2
  exact h2 h1

Conclusion ""
