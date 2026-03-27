import Game.Levels.TimWorld.L05_Tim

World "TimWorld"
Level 6

Title "Test"

Introduction "
### **🤔 Level 6?**
"


Statement (P Q R: Prop) (h1 : P ∧ Q) (h2 : P → (Q → R)) : R := by
  rw[← curry] at h2
  exact h2 h1

Conclusion ""
