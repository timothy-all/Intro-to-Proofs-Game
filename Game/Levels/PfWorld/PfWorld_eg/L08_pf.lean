import Game.Levels.PfWorld.PfWorld_eg.L07_pf

World "PfWorld_eg"
Level 8

Title "Example 8"

Introduction "
### **Level 8**
"

Statement {u : Type} (F G : Set (Set u)) : ⋂₀ F ∩ ⋂₀ G ⊆ ⋂₀ (F ∪ G) := by
  intro x ⟨hxF,hxG⟩ X hX -- or destructure with obtain
  rw[mem_union_iff] at hX
  obtain xF | xG := hX -- or rcases with ...
  exact hxF X xF
  exact hxG X xG

Conclusion ""
