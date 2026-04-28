import Game.Levels.SetWorld.SetWorld_eg.L07_set

World "SetWorld_eg"
Level 8

Title "name"

Introduction "
### **Level 8**
"

set_option pp.parens true


Statement {u : Type*} {I : Type*} (A B : I → Set u) : ⋂ i, (A i \ B i) = (⋂ i, A i ) \ (⋃ i, B i) := by
  apply Set.ext
  intro x
  rw[mem_iinter]
  rw[Set.mem_diff]
  rw[mem_iinter]
  rw[mem_iunion]
  push_neg
  exact forall_and




Conclusion ""
