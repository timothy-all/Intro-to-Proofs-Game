import Game.Levels.EquivWorld.EquivWorld_eg.L06_equiv

World "EquivWorld_eg"
Level 7

Title "Example 7"

Introduction "
### **Level 7**
"

set_option pp.parens true

Statement (P Q : Prop) : ((P ⊼ P) ⊼ (Q ⊼ Q)) ↔ (P ∨ Q) := by
  rw[Nand_self]
  rw[Nand_self]
  rw[Nand]
  rw[Not_and]
  rw[Not_not,Not_not]


Conclusion ""
