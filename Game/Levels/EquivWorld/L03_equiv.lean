import Game.Levels.EquivWorld.L02_equiv

World "EquivWorld"
Level 3

Title "Test"

Introduction "
### **🤔 Level 3?**
"

set_option pp.parens true


Statement (P Q R : Prop) : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  rw[← Or_imp]
  rw[Not_or]
  rw[Or_comm]
  rw[Or_and_left]
  rw[Or_comm]
  rw[Or_imp]
  rw[Or_comm]
  rw[Or_imp]


Conclusion ""
