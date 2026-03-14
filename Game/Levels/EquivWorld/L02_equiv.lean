import Game.Levels.EquivWorld.L01_equiv

World "EquivWorld"
Level 2

Title "Test"

Introduction "
### **🤔 Level 2?**

"


Statement (P Q : Prop) : (P → Q) ↔ (P ∧ Q) ∨ ¬ P := by
  rw[← conditional_law]
  rw[and_or_right]
  rw[or_not_self]
  rw[true_and]
  rw[or_comm]


Conclusion ""
