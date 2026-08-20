import Game.Levels.PfWorld.L11_pf

World "PfWorld"
Level 12

Title "Example 12"

Introduction "
### **Level 12**
"

Statement {u : Type*} (A B C: Set u) (x : u) : x ∈ A Δ (B Δ C) → x ∈ A ∧ x ∈ B → x ∈ A ∩ B ∩ C := by
  intro hx hxab
  constructor
  exact hxab
  obtain ⟨_,t1⟩ | t2 := hx
  rw[mem_symm_diff_iff] at t1
  rw[mem_union_iff] at t1
  rw[Not_or] at t1
  rw[mem_diff_iff] at t1
  rw[Not_and] at t1
  rw[Not_not] at t1
  obtain this := t1.left
  rw[← Imp_iff_not_or] at this
  exact this hxab.right
  rw[mem_diff_iff] at t2
  obtain ⟨this,_⟩ := t2
  obtain ⟨that,_⟩ := hxab
  contradiction

example {u : Type*} (A B C : Set u) (h : A Δ B ⊆ C) (hb : B ⊆ C) (hb' : Bᶜ ⊆ A): ∀ x, x ∈ C := by
  intro x
  by_cases hxb : x ∈ B
  exact hb hxb
  obtain hxa := hb' hxb
  obtain want : x ∈ A Δ B
  left
  exact And.intro hxa hxb
  exact h want





Conclusion ""
