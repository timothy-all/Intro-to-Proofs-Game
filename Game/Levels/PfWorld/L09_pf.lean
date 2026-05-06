import Game.Levels.PfWorld.L08_pf
import Mathlib.Tactic.Ring

World "PfWorld"
Level 9

Title "Example 9"

Introduction "
### **Level 9**
"

Statement (u : Type*) (A B : Set u) : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B → (A ⊆ B ∨ B ⊆ A) := by
  contrapose!
  intro ⟨h1,h2⟩
  rw[subset_def] at h1
  push_neg at h1
  rw[subset_def] at h2
  push_neg at h2
  rcases h1 with ⟨a,ha⟩
  rcases h2 with ⟨b,hb⟩
  simp
  rw[Set.ext_iff]
  push_neg
  use {a,b}
  constructor
  constructor
  intro x hx
  cases hx
  rw[h]
  left
  exact ha.left
  cases h
  right
  exact hb.left
  simp
  constructor
  rw[subset_def]
  push_neg
  use b
  simp
  exact hb.right
  rw[subset_def]
  push_neg
  use a
  simp
  exact ha.right













Conclusion ""
