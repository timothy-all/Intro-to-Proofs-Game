import Game.Levels.EquivWorld.L04_equiv

World "EquivWorld"
Level 5

Title "Test"

Introduction "
### **🤔 Level 5?**
"

set_option pp.parens true



Statement (P Q R : Prop) : (P → (Q ∨ R)) ↔ (¬ R → (P → Q)) := by
  rw[← Or_imp,← Or_imp]
  rw[Not_not]
  rw[← Or_imp]
  rw[Or_comm Q] -- tricky since or_comm has implicit arguments
  rw[← Or_assoc]
  rw[Or_comm (¬ P)] -- ditto
  rw[Or_assoc]


Conclusion ""
