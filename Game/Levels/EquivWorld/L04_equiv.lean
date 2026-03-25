import Game.Levels.EquivWorld.L03_equiv

World "EquivWorld"
Level 4

Title "Targeted Rewrites"

Introduction "
## **Level 4**

"

set_option pp.parens true


Statement (P Q R S : Prop) : (P ∧ Q) ∧ (R ∧ S) ↔ (P ∧ S) ∧ (R ∧ Q) := by
  rw[And_assoc]
  rw[← And_assoc Q]
  rw[And_comm (Q ∧ R)]
  rw[← And_assoc]
  rw[And_comm Q]




Conclusion ""
