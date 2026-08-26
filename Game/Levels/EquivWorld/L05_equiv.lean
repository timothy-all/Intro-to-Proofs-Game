import Game.Levels.EquivWorld.L04_equiv

World "EquivWorld"
Level 5

Title "Proof-by-contradiction"

Introduction "
# **Level 5: Proof-by-contradiction**
"

set_option pp.parens true

Statement (P Q : Prop) : (¬ P → False) ↔ P := by
  rw[Imp_iff_not_or]
  rw[Not_not]
  rw[Or_false]

Conclusion "
"

NewTheorem Or_false
