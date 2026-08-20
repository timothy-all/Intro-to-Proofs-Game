import Game.Levels.PfWorld.PfWorld_eg.L10_pf

World "PfWorld_eg"
Level 11

Title "Example 11"

Introduction "
### **Level 11**
"

Statement {u : Type*} (A B C : Set u) : A ∩ C = ∅ → A \ (B \ C) ⊆ (A \ B) \ C := by
  intro h x ⟨hxA,hxBC⟩
  refine ⟨⟨hxA,?_⟩,?_⟩
  rw[mem_diff_iff] at hxBC
  rw[Not_and] at hxBC
  obtain hxB' | hxC := hxBC
  exact hxB'
  rw[Not_not] at hxC
  obtain hxAC : x ∈ A ∩ C := And.intro hxA hxC
  rw[h] at hxAC
  contradiction
  rw[mem_diff_iff] at hxBC
  rw[Not_and] at hxBC
  obtain hxB' | hxC := hxBC
  by_contra! F
  obtain hxAC : x ∈ A ∩ C := And.intro hxA F
  rw[h] at hxAC
  contradiction
  rw[Not_not] at hxC
  obtain hxAC : x ∈ A ∩ C := And.intro hxA hxC
  rw[h] at hxAC
  contradiction

Conclusion ""
