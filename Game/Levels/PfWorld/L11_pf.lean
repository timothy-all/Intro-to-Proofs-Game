import Game.Levels.PfWorld.L10_pf

World "PfWorld"
Level 11

Title "Example 11"

Introduction "
# **Level 11**
"

open Set

Statement  {u : Type*} (A B : Set u) : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B → (A ⊆ B ∨ B ⊆ A) := by
  intro h
  rw[set_eq_iff] at h
  by_cases hAB : A ⊆ B
  left
  exact hAB
  right
  rw[subset_iff] at hAB
  rw[Not_forall] at hAB
  obtain ⟨a,ha⟩ := hAB
  rw[Imp_iff_not_or,Not_or,Not_not] at ha
  intro b hb
  obtain hab := h {a,b}
  obtain hab_left : {a,b} ∈ 𝒫 (A ∪ B)
  rw[mem_powerset_iff]
  intro x hx
  obtain xa | xb := hx
  left
  rw[xa]
  exact ha.left
  right
  rw[xb]
  exact hb
  rw[hab] at hab_left
  obtain T | F := hab_left
  rw[mem_powerset_iff] at T
  apply T
  right
  rfl
  obtain F' : a ∈ B
  rw[mem_powerset_iff] at F
  apply F
  left
  rfl
  obtain F'' := ha.right
  contradiction


Conclusion ""

<<<<<<< HEAD
NewTactic by_cases
=======
NewTactic exist!
>>>>>>> 0e46092 (Initial FunctionWorld docs. Changed use! to exist! and refactored where needed)
