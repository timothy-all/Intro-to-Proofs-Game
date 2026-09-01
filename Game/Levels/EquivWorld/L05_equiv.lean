import Game.Levels.EquivWorld.L04_equiv

World "EquivWorld"
Level 5

Title "Proof-by-contradiction"

Introduction "
# **Level 5: Proof-by-contradiction**
This logical equivalence is sometimes called **Proof-by-contradiction**. It says that `¬ P` implies `False` is true if and only if `P` is true. In other words, in order to prove that $P$ is true, it suffices to show that $¬ P$ leads to false.
"

set_option pp.parens true

/-- Not $P$ implies **False** if and only if $P$.-/
Statement (P Q : Prop) : (¬ P → False) ↔ P := by
  rw[Imp_iff_not_or]
  rw[Not_not]
  Hint "***Great.*** You can finish this level off with the now 🔓 unlocked theorem `Or_false`."
  rw[Or_false]

Conclusion "
We'll use this method of proof a lot in the future.
"

NewTheorem Or_false
