import Game.Levels.EquivWorld.EquivWorld_eg.L08_equiv

World "EquivWorld_eg"
Level 9

Title "Example 9"

Introduction "
### **Level 9**
"

set_option pp.parens true

Statement (P Q R S : Prop) : ((P ∧ Q) → (R ∨ S)) ↔ ((P → R) ∨ (Q → S)) := by
  rw[Imp_iff_not_or,Imp_iff_not_or,Imp_iff_not_or]
  rw[Not_and]
  rw[Or_assoc]
  rw[← Or_assoc (¬ Q)]
  rw[Or_comm _ R]
  rw[Or_assoc R]
  rw[← Or_assoc]

Conclusion ""
