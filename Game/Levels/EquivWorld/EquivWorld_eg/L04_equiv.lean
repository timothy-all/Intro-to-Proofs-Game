import Game.Levels.EquivWorld.L06_equiv

World "EquivWorld"
Level 7

Title "Test"

Introduction "
### **🤔 Level 7?**

"

set_option pp.parens true

/-- True_and doc -/
TheoremDoc True_and as "True_and"


Statement (P Q : Prop) : (P → Q) ↔ (P ∧ Q) ∨ ¬ P := by
  rw[← Or_imp]
  rw[Or_comm _ (¬ P)]
  rw[Or_and_left]
  rw[Or_comm (¬ P) P]
  rw[Or_not_self]
  rw[True_and]

Conclusion ""

NewTheorem True_and
