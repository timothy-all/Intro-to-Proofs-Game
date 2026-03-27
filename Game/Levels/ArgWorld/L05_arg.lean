import Game.Levels.TimWorld.L04_Tim

World "TimWorld"
Level 5

Title "Test"

Introduction "
### **🤔 Level 5?**
"

Statement (P : Prop) (h : ¬ P → False) : P := by
  rw[← Or_imp] at h
  rw[Not_not] at h
  rw[Or_false] at h
  exact h

Conclusion ""
