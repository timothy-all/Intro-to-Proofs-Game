import Mathlib.Data.Set.Lattice

theorem set_eq_iff {u : Type*} (A B : Set u) : A = B ↔ ∀ x : u, x ∈ A ↔ x ∈ B := by
  exact Set.ext_iff

theorem mem_union_iff {u : Type*} {x : u} (A B : Set u) : x ∈ A ∪ B ↔ (x ∈ A ∨ x ∈ B) := by
  simp

/-
theorem mem_inter_iff {u : Type*} {x : u} (A B : Set u) : x ∈ A ∩ B ↔ (x ∈ A ∧ x ∈ B) := by
  simp
-/

theorem mem_diff_iff {u : Type*} {x : u} (A B : Set u) : x ∈ A \ B ↔ (x ∈ A ∧ x ∉ B) := by
  simp

def symm_diff {u : Type*} (A B : Set u) := (A \ B) ∪ (B \ A)
infix:70 " Δ " => symm_diff

theorem mem_symm_diff_iff {u : Type*} {x : u} (A B : Set u) : x ∈ (A Δ B) ↔ x ∈ (A \ B) ∪ (B \ A) := by
  unfold symm_diff
  rfl

theorem mem_univ_iff_true {u : Type*} (a : u) : a ∈ Set.univ ↔ True := by
  simp

/- Families-/

theorem mem_iunion_iff {u : Type*} {x : u} {I : Type*} (A : I → Set u) : x ∈ ⋃ i, A i ↔ ∃ (i : I), x ∈ A i := by
  simp

theorem mem_iinter_iff {u : Type*} {x : u} {I : Type*} (A : I → Set u) : x ∈ ⋂ i, A i ↔ ∀ (i : I), x ∈ A i := by
  simp

theorem mem_finter_iff {u : Type*} {x : u} (F : Set (Set u)) : x ∈ ⋂₀ F ↔ ∀ (t : Set u), t ∈ F → x ∈ t := by
  simp

theorem mem_funion_iff {u : Type*} {x : u} (F : Set (Set u)) : x ∈ ⋃₀ F ↔ ∃ t ∈ F, x ∈ t := by
  simp

theorem subset_iff {u : Type*} {A B : Set u} : A ⊆ B ↔ ∀ {x}, x ∈ A → x ∈ B := by
  rw[Set.subset_def]
