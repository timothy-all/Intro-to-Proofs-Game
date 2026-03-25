import Game.Levels.EquivWorld.EquivWorld_eg.L02_equiv

World "EquivWorld_eg"
Level 3

Title "Example 3"

Introduction "
### **Level 3**

"

set_option pp.parens true

/-- Not_and doc -/
TheoremDoc Not_and as "Not_and"

/-- Or_not_self -/
TheoremDoc Or_not_self as "Or_not_self"

/-- And_true -/
TheoremDoc And_true as "And_true"

Statement (P Q : Prop) : (¬ ((P ∨ Q) ∧ (¬ P ∧ (Q → P)))) ↔ True := by
  rw[Not_and]
  rw[← Or_imp]
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
