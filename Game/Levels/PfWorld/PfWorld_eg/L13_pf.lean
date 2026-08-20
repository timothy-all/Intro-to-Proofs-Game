import Game.Levels.PfWorld.PfWorld_eg.L12_pf

World "PfWorld_eg"
Level 13

Title "Example 13"

Introduction "
### **Level 13**
"

Statement {u : Type*} (U : Set u) : ∀ A ⊆ U, ∃! B ⊆ U, A Δ B = ∅ := by
  intro A hA
  use! A
  refine ⟨hA,Symm_diff_self⟩
  intro B hB
  rw[set_eq_iff]
  intro x
  refine ⟨?_,?_⟩
  intro hxB
  by_contra!
  obtain that : x ∈ A Δ B
  right
  exact And.intro hxB this
  rw[hB.right] at that
  contradiction
  intro hxA
  by_contra!
  obtain that : x ∈ A Δ B
  left
  exact And.intro hxA this
  rw[hB.right] at that
  contradiction

Conclusion ""
