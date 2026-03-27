import Game.Levels.EquivWorld.EquivWorld_eg.L07_equiv

World "EquivWorld_eg"
Level 8

Title "Example 8"

Introduction "
### **Level 8**
"

set_option pp.parens true

Statement (P Q R : Prop) : ((P ⊻ Q) → R) ↔ ( (P ↔ Q) ∨ R) := by
  rw[xor_def]
  rw[Imp_iff_not_or]
  rw[Not_or]
  rw[Not_and,Not_and]
  rw[Not_not,Not_not]
  rw[← Imp_iff_not_or, ← Imp_iff_not_or]
  rw[← iff_def]


Conclusion ""
