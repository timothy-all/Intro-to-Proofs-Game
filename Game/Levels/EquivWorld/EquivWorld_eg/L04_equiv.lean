import Game.Levels.EquivWorld.EquivWorld_eg.L03_equiv

World "EquivWorld_eg"
Level 4

Title "Tautologies"

Introduction "
### **Level 4**
A statement like the one (on the left-hand side) of this example is what's called a **tautology**. This is a compound proposition that is `True` for every choice of true/false values of its constituent parts (in this case, `P` and `Q`).

We've unlocked a few more laws of logic for this example. 🔍 Check out the entries for `Or_not_self`, and `And_true` in the **Theorems** tab.
"

set_option pp.parens true

Statement (P Q : Prop) : P → (P ∨ Q) ↔ True := by
  rw[Imp_iff_not_or]
  rw[← Or_assoc]
  rw[Or_comm (¬ P)]
  rw[Or_not_self]
  rw[Or_comm]
  rw[Or_true]

Conclusion ""

NewTheorem Or_not_self Or_true
