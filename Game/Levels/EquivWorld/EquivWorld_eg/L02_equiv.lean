import Game.Levels.EquivWorld.EquivWorld_eg.L01_equiv

World "EquivWorld_eg"
Level 2

Title "Psuedo Conditional Law"

Introduction "
# **Level 2: Psuedo Conditional Law**
No new laws of logic needed here. But we will need to use some *targeted rewrites*.
"

set_option pp.parens true

/-- A pseudo contrapositive statement for implications with an `∨` statement as the conclusion.-/
Statement Imp_or_iff_imp_not_imp (P Q R : Prop) : (P → (Q ∨ R)) ↔ (P → (¬ Q → R)) := by
  rw[← Curry]
  rw[Imp_iff_not_or (P ∧ ¬ Q)]
  rw[Not_and]
  rw[Not_not]
  rw[Or_assoc]
  rw[← Imp_iff_not_or]


Conclusion "### **💡 Pro-tip**
The result of this level tells you that if you want to prove and if-then statement where the conclusion is a disjunction, then you may do so by... **assuming** that `P` and `¬ Q` are true, and then showing that `R` must follow."
