import Game.Levels.PfWorld.PfWorld_eg.L02_pf

World "PfWorld_eg"
Level 3

Title "Example 3"

Introduction "
### **Level 3**
"

Statement (P Q : Prop) (h1 : P → Q) (h2 : ¬ P → Q) : Q := by
  by_contra F
  rw[Contrapositive] at h2 h1
  rw[Not_not] at h2
  exact (h1 F) (h2 F)











Conclusion ""
