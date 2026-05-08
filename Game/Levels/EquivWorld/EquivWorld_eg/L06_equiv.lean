import Game.Levels.EquivWorld.EquivWorld_eg.L05_equiv

World "EquivWorld_eg"
Level 6

Title "And and Nand"

Introduction "
### **Level 6**
Here's another logical equivalence involving `⊼`.
"

set_option pp.parens true

Statement (P Q : Prop) : ((P ⊼ Q) ⊼ (P ⊼ Q)) ↔ (P ∧ Q) := by
  rw[Nand_self]
  rw[nand_def]
  rw[Not_not]


Conclusion "### **🤔 More food for thought**
The binary operator `∧` can be expressed in terms of `⊼` too ..."
