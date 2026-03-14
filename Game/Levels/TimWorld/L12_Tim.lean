import Game.Levels.TimWorld.L11_Tim

World "TimWorld"
Level 12

Title "Test"

Introduction "
### **🤔 Level 12?**
"

theorem test1 (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) := by
  sorry


Statement test (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  rw[test1]






Conclusion ""

NewTactic obtain
