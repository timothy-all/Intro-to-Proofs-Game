import Game.Levels.EquivWorld.EquivWorld_eg.L02_equiv

World "EquivWorld_eg"
Level 3

Title "Contradictions"

Introduction "
# **Level 3: Contradictions **
A statement like the one (on the left-hand side) of this example is what's called a **contradiction**. This is a compound proposition that is `False` for every choice of true/false values of its constituent parts (in this case, `P` and `Q`).

We've unlocked a few more laws of logic for this example. 🔍 Check out the entries for `Not_and`, `And_not_self`, and `Or_false` in the **Theorems** tab.
"

set_option pp.parens true

/-- There's no choice of `True` or `False` values for `P` and `Q` that would make the left-hand statement on the left-hand side of this iff true.-/
Statement (P Q : Prop) : ((P ∨ Q) ∧ (¬ P ∧ (Q → P))) ↔ False := by
  rw[Imp_iff_not_or]
  rw[And_or_left]
  rw[And_comm (¬ P) P]
  rw[And_not_self]
  rw[Or_false]
  rw[← Not_or]
  rw[And_not_self]

Conclusion "The world's most canonical contradiction is undoubtedly `P ∧ ¬ P`."

NewTheorem Not_and And_not_self Or_false And_or_left
