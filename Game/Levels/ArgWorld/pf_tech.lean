import Game.Levels.ArgWorld.L07_arg

World "ArgWorld"
Level 8

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
  rw[contrapositive] at h2 h1
  rw[Not_not] at h2
  exact (h1 F) (h2 F)

Conclusion ""
