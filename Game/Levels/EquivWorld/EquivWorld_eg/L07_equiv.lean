import Game.Levels.EquivWorld.EquivWorld_eg.L06_equiv

World "EquivWorld_eg"
Level 7

Title "Or and Nand"

Introduction "
### **Level 7**
One last example involving `⊼`. Are you noticing something interesting?
"

set_option pp.parens true

Statement (P Q : Prop) : ((P ⊼ P) ⊼ (Q ⊼ Q)) ↔ (P ∨ Q) := by
  rw[Nand_self]
  rw[Nand_self]
  rw[nand_def]
  rw[Not_and]
  rw[Not_not,Not_not]


Conclusion "### **🤔 All the food for thought**
The binary operator `∨` can be expressed in terms of `⊼` ... can everything be expressed in terms of `⊼`?!"
