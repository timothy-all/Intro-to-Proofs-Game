import Game.Levels.PfWorld.L06_pf

World "PfWorld"
Level 7

Title "Example 7"

Introduction "
### **Level 7**
"

Statement (u : Type*) (F G : Set (Set u)) : ⋃₀ F ∩ ⋃₀ G ⊆ ⋃₀ (F ∩ G) ↔ ∀ A ∈ F, ∀ B ∈ G, A ∩ B ⊆ ⋃₀ (F ∩ G) := by
  constructor
  intro h A hA B hB x hx
  apply h
  constructor
  use A
  refine ⟨hA,hx.left⟩
  use B
  refine ⟨hB,hx.right⟩
  intro h x hx
  obtain ⟨A,hA,hxA⟩ := hx.left
  obtain ⟨B,hB,hxB⟩ := hx.right
  obtain hAB := h A hA B hB
  apply hAB
  exact And.intro hxA hxB

Conclusion ""

NewTactic refine apply
