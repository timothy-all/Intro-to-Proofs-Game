import Game.Levels.PfWorld.L12_pf

World "PfWorld"
Level 13

Title "Example 13"

Introduction "
### **Level 13**
"

Statement {u : Type*} (A B C : Set u) (h : A Δ B ⊆ C) (hb : B ⊆ C) (hb' : Bᶜ ⊆ A): ∀ x, x ∈ C := by
  intro x
  by_cases hxb : x ∈ B
  exact hb hxb
  obtain hxa := hb' hxb
  obtain want : x ∈ A Δ B
  left
  exact And.intro hxa hxb
  exact h want

Conclusion ""

NewTactic by_cases
