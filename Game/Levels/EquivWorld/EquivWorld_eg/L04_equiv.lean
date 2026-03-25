import Game.Levels.EquivWorld.EquivWorld_eg.L03_equiv

World "EquivWorld_eg"
Level 4

Title "Example 4"

Introduction "
### **Level 4**

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
