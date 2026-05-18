import Game.Levels.PfWorld.PfWorld_eg.L04_pf

World "PfWorld_eg"
Level 5

Title "Example 5"

Introduction "
### **Level 5**
"

Statement {u : Type} (F G : Set (Set u)) : ⋂₀ (F ∪ G) ⊆ ⋂₀ F ∩ ⋂₀ G  := by
  intro x hx
  refine ⟨?xinF,?xinG⟩
  intro X hXF
  obtain hXFG := Or.intro_left (X ∈ G) hXF
  rw[← Set.mem_union] at hXFG
  exact hx X hXFG
  intro X hXG
  obtain hXFG := Or.intro_right (X ∈ F) hXG
  rw[← Set.mem_union] at hXFG
  exact hx X hXFG

Conclusion ""
