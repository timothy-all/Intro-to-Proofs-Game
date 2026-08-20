import Game.Levels.PfWorld.L09_pf

World "PfWorld"
Level 10

Title "Example 10"

Introduction "
### **Level 10**
"

Statement (u : Type*) (A B C : Set u) : A ∪ C = B ∪ C → A Δ B ⊆ C := by
  intro h x hx
  obtain hxa | hxb := hx
  obtain hxAC : x ∈ A ∪ C
  left
  exact hxa.left
  rw[h] at hxAC
  obtain hxB | hxC := hxAC
  obtain hxB' := hxa.right
  contradiction
  exact hxC
  obtain hxBC : x ∈ B ∪ C
  left
  exact hxb.left
  rw[← h] at hxBC
  obtain hxA | hxC := hxBC
  obtain hxA' := hxb.right
  contradiction
  exact hxC


Conclusion ""
