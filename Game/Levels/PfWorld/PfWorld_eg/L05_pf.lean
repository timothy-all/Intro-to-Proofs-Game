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
  apply hx X
  left
  exact hXF
  intro X hXG
  apply hx X
  right
  exact hXG

Conclusion ""
