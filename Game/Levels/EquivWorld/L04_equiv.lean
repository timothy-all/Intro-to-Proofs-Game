import Game.Levels.EquivWorld.L03_equiv

World "EquivWorld"
Level 4

Title "Test"

Introduction "
### **🤔 Level 4?**
"

set_option pp.parens true

/--
Not_or doc
-/
TheoremDoc Not_or as "Not_or"

/--
Or_and_left doc
-/
TheoremDoc Or_and_left as "Or_and_left"

Statement (P Q R : Prop) : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  rw[← Or_imp]
  rw[Not_or]
  rw[Or_comm]
  rw[Or_and_left]
  rw[Or_comm]
  rw[Or_imp]
  rw[Or_comm]
  rw[Or_imp]


Conclusion ""

NewTheorem Not_or Or_and_left
