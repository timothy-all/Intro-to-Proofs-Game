import Game.Levels.ArgWorld.L02_arg

World "ArgWorld"
Level 3

Title "Disjunctive Syllogism"

Introduction "
### **Level 3**
This valid argument is sometimes referred to as the law of the **Disjunctive Syllogism**. Using some laws of logical equivalence, try to rewrite the hypothesis `h1` in a form that is more similar to the hypotheses of the last couple levels.
"


Statement (P Q : Prop) (h1 : P ∨ Q) (h2 : ¬ P) : Q := by
  rw[← Not_not P] at h1
  rw[← Imp_iff_not_or] at h1
  exact h1 h2

Conclusion "***💪 Challenge:*** Try to complete this level using only two tactic calls."
