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
  rw[mem_finter]
  intro B hB
  --change ¬ x ∈ ⋂₀ F at hF --real confusing: internally things changed but the terminal delaborates the same way
  rw[mem_finter] at hF
  push_neg at hF
  rcases hF with ⟨ A, hA,hxA'⟩
  obtain hAB := h A hA B hB
  obtain hx' := hx (A ∪ B) hAB
  rcases hx' with hxA | hxB
  contradiction
  exact hxB

Conclusion ""
