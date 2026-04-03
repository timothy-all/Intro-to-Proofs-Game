import Game.Levels.ArgWorld.L02_arg

World "ArgWorld"
Level 3

Title "Disjunctive Syllogism"

Introduction "
## **Level 3**
This valid argument is sometimes referred to as the law of the **disjunctive syllogism**. Using some laws of logical equivalence, try to rewrite the hypothesis `hPQ` in a form that is more similar to the hypotheses of the last couple levels.
"


Statement (P Q : Prop) (hPQ : P ∨ Q) (hnP : ¬ P) : Q := by
  rw[← Not_not P] at hPQ
  rw[← Imp_iff_not_or] at hPQ
  exact hPQ hnP

Conclusion ""
