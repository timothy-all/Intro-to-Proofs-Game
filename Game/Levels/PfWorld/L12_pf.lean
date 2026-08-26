import Game.Levels.PfWorld.L11_pf

World "PfWorld"
Level 12

Title "Example 12"

Introduction "
### **Level 12**
"

Statement {u : Type*} (A B C : Set u) (h : (A \ B ∪ B \ A) ⊆ C) (hB : B ⊆ C) (hB' : Bᶜ ⊆ A): ∀ x, x ∈ C := by
  intro x
  by_cases hxb : x ∈ B
  exact hB hxb
  obtain hxa := hB' hxb
  obtain want : x ∈ A Δ B
  left
  exact And.intro hxa hxb
  exact h want


Conclusion ""
