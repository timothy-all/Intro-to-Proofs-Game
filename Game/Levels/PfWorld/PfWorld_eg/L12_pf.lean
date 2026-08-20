import Game.Levels.PfWorld.PfWorld_eg.L11_pf

World "PfWorld_eg"
Level 12

Title "Example 12"

Introduction "
### **Level 12**
"

open Set

Statement {u : Type*} (U : Set u) : ∃! I ⊆ U, ∀ A ⊆ U, A Δ I = A := by
  use! ∅
  refine ⟨⟨?_,?_⟩,?_⟩
  intro x hx
  contradiction
  -- apply Set.empty_subset -- this works instead of intro/contradiction
  intro A hA
  rw[set_eq_iff]
  intro x
  refine ⟨?_,?_⟩
  intro hx
  rcases hx with ⟨hxA,F'⟩ | ⟨F,hxA'⟩
  exact hxA
  contradiction
  intro hxA
  left
  refine ⟨?_,?_⟩
  exact hxA
  by_contra!
  contradiction
  intro I hI
  by_contra!
  --rw[nonempty_def] at this
  rcases this with ⟨i,hi⟩
  obtain F := hI.right I hI.left
  rw[← F] at hi
  rw[Symm_diff_self] at hi
  contradiction

Conclusion ""
