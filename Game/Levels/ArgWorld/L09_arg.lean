import Game.Levels.TimWorld.L08_Tim

World "TimWorld"
Level 9

Title "Test"

Introduction "
### **🤔 Level 9?**
"

set_option pp.parens true

/--
obtain doc
-/
TacticDoc obtain

Statement (P Q : Prop) (h1 : P → Q) (h2 : ¬ P → Q) : Q := by
  by_contra F
  rw[Contrapos] at h2 h1
  rw[Not_not] at h2
  exact (h1 F) (h2 F)

Conclusion ""
