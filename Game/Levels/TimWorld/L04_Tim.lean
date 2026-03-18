import Game.Levels.TimWorld.L03_Tim

World "TimWorld"
Level 4

Title "Test"

Introduction "
### **🤔 Level 4?**
"


Statement (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬ P) : Q := by
  rw[← Not_not P] at h1
  rw[Or_imp] at h1
  exact h1 h2

Conclusion ""
