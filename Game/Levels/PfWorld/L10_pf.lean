import Game.Levels.PfWorld.L09_pf

World "PfWorld"
Level 10

Title "Example 10"

Introduction "
### **Level 10**
"

Statement (u : Type*) (A B C : Set u) : A ∪ C = B ∪ C → symmDiff A B ⊆ C := by
  intro h x hx
  rcases hx with hxa | hxb
  obtain hxAC : x ∈ A ∪ C
  left
  exact hxa.left
  rw[h] at hxAC
  rcases hxAC with hxB | hxC
  obtain hxB' := hxa.right
  contradiction
  exact hxC
  obtain hxBC : x ∈ B ∪ C
  left
  exact hxb.left
  rw[← h] at hxBC
  rcases hxBC with hxA | hxC
  obtain hxA' := hxb.right
  contradiction
  exact hxC


Conclusion ""
