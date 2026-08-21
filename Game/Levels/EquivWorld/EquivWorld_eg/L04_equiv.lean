import Game.Levels.EquivWorld.EquivWorld_eg.L03_equiv

World "EquivWorld_eg"
Level 4

Title "Tautologies"

Introduction "
# **Level 4: Tautologies**
A statement like the one (on the left-hand side) of this example is what's called a **tautology**. This is a compound proposition that is `True` for every choice of true/false values of its constituent parts (in this case, `P` and `Q`).

We've unlocked a few more laws of logic for this example. 🔍 Check out the entries for `Or_not_self`, and `And_true` in the **Theorems** tab.
"

set_option pp.parens true

/-- There's no choice of `True` or `False` values for `P` and `Q` that would make the left-hand statement on the left-hand side of this iff false.-/
Statement (P Q : Prop) : P → (P ∨ Q) ↔ True := by
  rw[Imp_iff_not_or]
  rw[← Or_assoc]
  rw[Or_comm (¬ P)]
  rw[Or_not_self]
  rw[Or_comm]
  rw[Or_true]

Conclusion "The world's most canonical tautology is undoubtedly `P ∨ ¬ P`."

NewTheorem Or_not_self Or_true And_false
