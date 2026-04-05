import Game.Levels.SetWorld

World "SetWorld_eg"
Level 1

Title "name"

Introduction "
### **Level 1**
"

Statement {u : Type} (A B : Set u) : A ∩ B = ∅ ↔ A ⊆ A \ B := by
  constructor
  intro ABe x hxA
  refine ⟨hxA,?_⟩
  by_contra!
  obtain F : x ∈ A ∩ B := And.intro hxA this
  rw[ABe] at F
  exact F
  intro h
  by_contra! F
  rcases F with ⟨x,hx⟩
  exact (h hx.left).right hx.right

Conclusion ""

theorem emp_def {u : Type} (A : Set u) : A = ∅ ↔ ¬ ∃ x, x ∈ A := by
  constructor
  intro h
  by_contra!
  rcases this with ⟨ x, hx⟩
  rw[h] at hx
  exact hx
  intro h
  by_contra!
  rcases this with ⟨x,hx⟩
  push_neg at h
  exact (h x) hx

example {u : Type} (A B : Set u) : A ∩ B = ∅ → A ⊆ A \ B := by
  rw[Set.eq_empty_iff_forall_notMem] -- pretty wordy
  intro h x hxA
  obtain hxB := h x
  rw[Set.mem_inter_iff] at hxB
  rw[Not_and,← Imp_iff_not_or] at hxB
  exact And.intro hxA (hxB hxA)
