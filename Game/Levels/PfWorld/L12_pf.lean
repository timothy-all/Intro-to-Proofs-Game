import Game.Levels.PfWorld.L11_pf

World "PfWorld"
Level 12

Title "Example 12"

Introduction "
### **Level 12**
"

Statement {u : Type*} (A B C: Set u) (x : u) : x ∈ symmDiff A (symmDiff B C) → x ∈ A ∧ x ∈ B → x ∈ A ∩ B ∩ C := by
  intro hx hxab
  refine ⟨hxab,?_⟩
  rcases hx with ⟨_,t1⟩ | t2
  rw[Set.mem_symmDiff] at t1
  push_neg at t1
  exact t1.left hxab.right
  rw[Set.mem_diff] at t2
  obtain this := hxab.left
  obtain that := t2.right
  contradiction

example {u : Type*} (A B C : Set u) (h : symmDiff A B ⊆ C) (hb : B ⊆ C) (hb' : Bᶜ ⊆ A): ∀ x, x ∈ C := by
  intro x
  by_cases hxb : x ∈ B
  exact hb hxb
  obtain hxa := hb' hxb
  obtain want : x ∈ symmDiff A B
  left
  exact And.intro hxa hxb
  exact h want





Conclusion ""
