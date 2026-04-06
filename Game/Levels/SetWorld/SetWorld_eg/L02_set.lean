import Game.Levels.SetWorld.SetWorld_eg.L01_set

World "SetWorld_eg"
Level 2

Title "name"

Introduction "
### **Level 2**
"
set_option pp.parens true

Statement {u : Type} (A B C : Set u) : (A \ B) \ C = A \ (B ∪ C) := by
  apply Set.ext
  intro x
  repeat rw[Set.mem_diff]
  rw[Set.mem_union]
  rw[Not_or]
  rw[And_assoc]



Conclusion ""
