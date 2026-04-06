import Game.Levels.SetWorld.SetWorld_eg.L01_set

World "SetWorld_eg"
Level 2

Title "name"

Introduction "
### **Level 2**
"

set_option pp.parens true

Statement {u : Type} (A B C : Set u) : A ∪ (B \ C) = (A ∪ B) \ (C \ A) := by
  apply Set.ext
  intro x
  rw[Set.mem_union]
  rw[Set.mem_diff]
  rw[Set.mem_diff]
  rw[Set.mem_union]
  rw[Set.mem_diff]
  rw[Not_and]
  rw[Or_and_left]
  rw[Or_comm (x ∈ A) (x ∉ C)]
  rw[Not_not]


Conclusion ""
