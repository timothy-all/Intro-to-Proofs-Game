import Game.Levels.EquivWorld.EquivWorld_eg.L04_equiv

World "EquivWorld_eg"
Level 5

Title "More practice"

Introduction "
# **Level 5: More practice**
No new laws of logic needed here either. But this example should provide good practice with what we've learned so far.
"

set_option pp.parens true

Statement (P Q : Prop) : (P → Q) ↔ (P ∧ Q) ∨ ¬ P := by
  rw[Imp_iff_not_or]
  rw[Or_comm _ (¬ P)]
  rw[Or_and_left]
  rw[Or_comm (¬ P) P]
  rw[Or_not_self]
  rw[And_comm]
  rw[And_true]

Conclusion ""

NewTheorem And_true
