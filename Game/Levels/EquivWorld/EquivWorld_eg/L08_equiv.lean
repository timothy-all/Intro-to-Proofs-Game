import Game.Levels.EquivWorld.EquivWorld_eg.L07_equiv

World "EquivWorld_eg"
Level 8

Title "Or and Nand"

Introduction "
# **Level 8: Or and Nand**
One last example involving `⊼`. Are you noticing something interesting?
"

set_option pp.parens true

Statement (P Q : Prop) : ((P ⊼ P) ⊼ (Q ⊼ Q)) ↔ (P ∨ Q) := by
  rw[Nand_self]
  rw[Nand_self]
  rw[nand_def]
  rw[Not_and]
  rw[Not_not,Not_not]


Conclusion "### **💡 All the food for thought**
The binary operator `∨` can be expressed in terms of `⊼`. The last three examples show that the unary operator `¬` and the binary operators `∨` and `∧` can be expressed in terms of `⊼`. In fact, *any* binary operator on `True` and `False` can be expressed in terms of `⊼`!"
