import Game.Levels.EquivWorld.L04_equiv

World "EquivWorld"
Level 5

Title "Test"

Introduction "
### **🤔 Level 5?**

"

set_option pp.parens true


Statement (P Q : Prop) : (¬ ((P ∨ Q) ∧ (¬ P ∧ (Q → P)))) ↔ True := by
  rw[Not_and]
  rw[← Or_imp]
  rw[Not_and]
  rw[Not_or (¬ Q)]
  rw[Not_not,Not_not]
  rw[Or_and_left]
  rw[Or_not_self]
  rw[And_true]
  rw[Or_comm]
  rw[Or_not_self]

Conclusion ""
