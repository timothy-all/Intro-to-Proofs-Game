import Mathlib.Data.Set.Lattice


theorem mem_iunion {u : Type*} {x : u} {I : Type*} (A : I → Set u) : x ∈ ⋃ i, A i ↔ ∃ (i : I), x ∈ A i := by
  simp

theorem mem_iinter {u : Type*} {x : u} {I : Type*} (A : I → Set u) : x ∈ ⋂ i, A i ↔ ∀ (i : I), x ∈ A i := by
  simp

theorem mem_finter {u : Type*} {x : u} (F : Set (Set u)) : x ∈ ⋂₀ F ↔ ∀ (t : Set u), t ∈ F → x ∈ t := by
  simp

theorem mem_funion {u : Type*} {x : u} (F : Set (Set u)) : x ∈ ⋃₀ F ↔ ∃ t ∈ F, x ∈ t := by
  simp

theorem mem_univ_iff_true {u : Type} (a : u) : a ∈ Set.univ ↔ True := by
  simp
