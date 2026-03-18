import Game.Levels.TimWorld.L01_Tim

World "TimWorld"
Level 2

Title "Test"

Introduction "
### **🤔 Level 2?**
"


Statement (P Q : Prop) (h1 : P → Q) (h2 : ¬ Q) : ¬ P := by
  rw[← Or_imp] at h1
  rw[← Not_not Q] at h1
  rw[Or_comm] at h1
  rw[Or_imp] at h1
  exact h1 h2


Conclusion ""
