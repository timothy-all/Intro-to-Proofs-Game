import Game.Levels.EquivWorld.EquivWorld_eg.L02_equiv

World "EquivWorld_eg"
Level 3

Title "Tautologies"

Introduction "
### **Level 3**
A statement like the one (on the left-hand side) of this example is what's called a **tautology**. This is a compound proposition that is `True` for every choice of true/false values of its constituent parts (in the case `P` and `Q`). We've unlocked a few more laws of logic for this example. 🔍 Check out the entries for `Not_and`, `Or_not_self`, and `And_true` in the **Theorems** tab.
"

set_option pp.parens true



Statement (P Q : Prop) : (¬ ((P ∨ Q) ∧ (¬ P ∧ (Q → P)))) ↔ True := by
  rw[Not_and]
  rw[Imp_iff_not_or]
  rw[Not_and]
  rw[Not_or (¬ Q)]
  rw[Not_not,Not_not]
  rw[Or_and_left]
  rw[Or_not_self]
  rw[And_true]
  rw[Or_comm]
  rw[Or_not_self]

Conclusion ""

NewTheorem Not_and Or_not_self And_true
