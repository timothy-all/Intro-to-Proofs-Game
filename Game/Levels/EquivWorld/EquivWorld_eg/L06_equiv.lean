import Game.Levels.EquivWorld.EquivWorld_eg.L05_equiv

World "EquivWorld_eg"
Level 6

Title "Example 6"

Introduction "
### **Level 6**
"

set_option pp.parens true

Statement (P Q : Prop) : ((P ⊼ Q) ⊼ (P ⊼ Q)) ↔ (P ∧ Q) := by
  rw[Nand_self]
  rw[Nand]
  rw[Not_not]


Conclusion ""
