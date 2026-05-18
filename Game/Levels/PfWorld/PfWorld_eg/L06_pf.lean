import Game.Levels.PfWorld.PfWorld_eg.L05_pf

World "PfWorld_eg"
Level 6

Title "Example 6"

Introduction "
### **Level 6**
"

Statement {u : Type*} (A B C : Set u) : (A \ B) \ C ⊆ A \ (B \ C) := by
  intro x hx
  constructor
  exact hx.left.left
  rw[Set.mem_diff]
  rw[Not_and]
  left
  rcases hx with ⟨ ⟨hxA, hxB'⟩,hxC'⟩
  exact hxB'

Conclusion ""
