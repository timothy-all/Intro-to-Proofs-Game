import Game.Levels.ArgWorld.L02_arg

World "ArgWorld"
Level 3

Title "Disjunctive Syllogism"

Introduction "
# **Level 3**
This valid argument is sometimes referred to as the law of the **Disjunctive Syllogism**. Using some laws of logical equivalence, try to rewrite the hypothesis `h1` in a form that is more similar to the hypotheses of the last couple levels.
"

/-- This valid argument is known as *Disjunctive Syllogism*.-/
Statement (P Q : Prop) (hPorQ : P ∨ Q) (nP : ¬ P) : Q := by
  rw[← Not_not P] at hPorQ
  rw[← Imp_iff_not_or] at hPorQ
  exact hPorQ nP

Conclusion "***💪 Challenge:*** Try to complete this level using only two tactic calls."
