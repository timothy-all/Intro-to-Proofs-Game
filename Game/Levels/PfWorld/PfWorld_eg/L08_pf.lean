import Game.Levels.PfWorld.PfWorld_eg.L07_pf

World "PfWorld_eg"
Level 8

Title "Example 8"

Introduction "
### **Level 8**
"

Statement {u : Type} (F G : Set (Set u)) : ⋂₀ F ∩ ⋂₀ G ⊆ ⋂₀ (F ∪ G) := by
  intro x ⟨hxF,hxG⟩ X hX -- or destructure with obtain
  rw[Set.mem_union] at hX
  cases hX -- or rcases with ...
  exact hxF X h
  exact hxG X h

Conclusion ""
