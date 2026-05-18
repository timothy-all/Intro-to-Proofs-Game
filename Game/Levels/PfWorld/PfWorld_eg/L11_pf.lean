import Game.Levels.PfWorld.PfWorld_eg.L10_pf

World "PfWorld_eg"
Level 11

Title "Example 11"

Introduction "
### **Level 11**
"

Statement {u : Type*} (A B C : Set u) : A ∩ C = ∅ → A \ (B \ C) ⊆ (A \ B) \ C := by
  intro h x ⟨hxA,hxBC⟩
  constructor
  constructor
  exact hxA
  rw[Set.mem_diff] at hxBC
  rw[Not_and] at hxBC
  rcases hxBC with hxB' | hxC
  exact hxB'
  rw[Not_not] at hxC
  obtain hxAC : x ∈ A ∩ C := And.intro hxA hxC
  rw[h] at hxAC
  contradiction
  rw[Set.mem_diff] at hxBC
  rw[Not_and] at hxBC
  rcases hxBC with hxB' | hxC
  by_contra! F
  obtain hxAC : x ∈ A ∩ C := And.intro hxA F
  rw[h] at hxAC
  contradiction
  rw[Not_not] at hxC
  obtain hxAC : x ∈ A ∩ C := And.intro hxA hxC
  rw[h] at hxAC
  contradiction

Conclusion ""
