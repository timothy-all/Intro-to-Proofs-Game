import Game.Levels.ArgWorld.L02_arg

World "ArgWorld"
Level 3

Title "Disjunctive Syllogism"

Introduction "
### **Level 3**
"


Statement (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬ P) : Q := by
  rw[← Not_not P] at h1
  rw[← Imp_iff_not_or] at h1
  exact h1 h2

Conclusion ""
