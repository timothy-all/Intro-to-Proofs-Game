import Game.Levels.EquivWorld.EquivWorld_eg.L04_equiv

World "EquivWorld_eg"
Level 5

Title "Example 5"

Introduction "
### **Level 5**
"

set_option pp.parens true

/--
Nand_self
-/
TheoremDoc Nand_self as "Nand_self"

Statement Nand_self (P : Prop) : (P ⊼ P) ↔ ¬ P := by
  rw[nand_def]
  rw[Not_and]
  rw[Or_self]

Conclusion ""
