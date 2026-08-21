import Game.Levels.EquivWorld.EquivWorld_eg.L04_equiv

World "EquivWorld_eg"
Level 5

Title "More practice"

Introduction "
# **Level 5: More practice**
We've unlocked the theorem `And_true` for this level. 🔍 Check out the entry for this theorem in the **Theorems** tab. It's not strictly necessary for this level, but it might come in handy depending on your approach.
"

set_option pp.parens true

/-- The statement *`P` implies `Q`* is logically equivalent to *`P` and `Q`, or not `P`*.-/
Statement (P Q : Prop) : (P → Q) ↔ (P ∧ Q) ∨ ¬ P := by
  rw[Imp_iff_not_or]
  rw[Or_comm _ (¬ P)]
  rw[Or_and_left]
  rw[Or_comm (¬ P) P]
  rw[Or_not_self]
  rw[And_comm]
  rw[And_true]

Conclusion "### ** 💡 Pro-tip
Generally speaking, there are lots of ways to go about these proofs (depending on what you know). Did you use `And_true` in your proof? If not, go back and find a way to use it in the proof. If so, go back and find a way to *not* use it."

NewTheorem And_true
