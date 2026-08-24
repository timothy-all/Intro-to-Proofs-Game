import Game.Levels.SetWorld.SetWorld_eg.L07_set

World "SetWorld_eg"
Level 8

Title "name"

Introduction "
### **Level 8**
"

--set_option pp.parens true

open Set

/-- This statement says

$$ \displaystyle ⋂_{i ∈ I} A_i \setminus B_i = $$
 -/
Statement {u : Type*} {I : Type*} (A B : I → Set u) : ⋂ i, (A i \ B i) = (⋂ i, A i ) \ (⋃ i, B i) := by
  rw[set_eq_iff]
  intro x
  rw[mem_iinter_iff]
  rw[mem_diff_iff]
  rw[mem_iinter_iff]
  rw[mem_iunion_iff]
  push_neg
  exact Forall_and  --hmm

Conclusion ""

NewDefinition mem_iunion_iff
