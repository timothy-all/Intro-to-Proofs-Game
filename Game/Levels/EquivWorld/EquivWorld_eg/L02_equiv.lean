import Game.Levels.EquivWorld.EquivWorld_eg.L01_equiv

World "EquivWorld_eg"
Level 2

Title "Example 2"

Introduction "
### **Level 2**
No new laws of logic needed here. But we will need to use some *targeted* rewrites.
"

set_option pp.parens true

Statement (P Q R : Prop) : (P → (Q ∨ R)) ↔ (¬ R → (P → Q)) := by
  rw[Imp_iff_not_or,Imp_iff_not_or]
  rw[Not_not]
  rw[Imp_iff_not_or]
  rw[Or_comm Q] -- tricky since or_comm has implicit arguments
  rw[← Or_assoc]
  rw[Or_comm (¬ P)] -- ditto
  rw[Or_assoc]


Conclusion ""
