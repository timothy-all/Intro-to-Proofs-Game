import Game.Levels.PfWorld.PfWorld_eg.L13_pf

World "PfWorld_eg"
Level 14

Title "Example 14"

Introduction "
### **Level 14**
"

Statement {u : Type*} (F G H : Set (Set u)) : (∀ A ∈ F, ∀ B ∈ G, A ∪ B ∈ H) → ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := by
  intro h x hx
  by_cases hF : x ∈ ⋂₀ F
  left
  exact hF
  right
  rw[mem_finter_iff]
  intro B hB
  --change ¬ x ∈ ⋂₀ F at hF --real confusing: internally things changed but the terminal delaborates the same way
  rw[mem_finter_iff] at hF
  push_neg at hF
  obtain ⟨ A, hA,hxA'⟩ := hF
  obtain hAB := h A hA B hB
  obtain hxA | hxB := hx (A ∪ B) hAB
  contradiction
  exact hxB

Conclusion ""
