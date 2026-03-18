import Game.Levels.EquivWorld

World "TimWorld"
Level 1

Title "Test"

Introduction "
### **🤔 Level 1?**

"

/--
Exact doc
-/
TacticDoc exact

Statement (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
  exact h2 h1

Conclusion ""

NewTactic exact
