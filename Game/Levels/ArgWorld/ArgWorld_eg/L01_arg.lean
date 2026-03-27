import Game.Levels.ArgWorld

World "ArgWorld_eg"
Level 1

Title "Rule of Contradiction"

Introduction "
### **Level 1**
"

Statement (P : Prop) (h : ¬ P → False) : P := by
  rw[Imp_iff_not_or] at h
  rw[Not_not] at h
  rw[Or_false] at h
  exact h

Conclusion ""

NewTheorem Or_false
