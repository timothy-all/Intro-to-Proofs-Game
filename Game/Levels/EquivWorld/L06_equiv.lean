import Game.Levels.EquivWorld.L05_equiv

World "EquivWorld"
Level 6

Title "Test"

Introduction "
### **🤔 Level 6?**

"

set_option pp.parens true




Statement (P Q : Prop) : (P → Q) ↔ (P ∧ Q) ∨ ¬ P := by
  rw[← Or_imp]
  rw[Or_comm _ (¬ P)]
  rw[Or_and_left]
  rw[Or_comm (¬ P) P]
  rw[Or_not_self]
  rw[true_and]

Conclusion ""

NewTheorem Not_and Or_assoc
NewTactic rw
