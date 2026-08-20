import Game.Levels.PfWorld.L08_pf

World "PfWorld"
Level 9

Title "Example 9"

Introduction "
### **Level 9**
"

open Set

Statement (u : Type*) (A B : Set u) : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B → (A ⊆ B ∨ B ⊆ A) := by
  contrapose --using contrapose! might be a mistake...
  intro h
  rw[Not_or] at h
  rw[subset_iff,subset_iff] at h
  push_neg at h
  obtain ⟨a,ha⟩ := h.left
  obtain ⟨b,hb⟩ := h.right
  rw[set_eq_iff]
  push_neg
  use {a,b}
  constructor
  constructor
  intro x hx
  obtain xa | xb := hx
  left
  rw[xa]
  exact ha.left
  right
  rw[xb]
  exact hb.left
  rw[mem_union_iff]
  push_neg
  constructor
  rw[mem_powerset_iff]
  rw[subset_iff]
  push_neg
  use b
  constructor
  right
  /-
  It seems x ∈ {a,b} is shorthand for x = a ∨ x ∈ {b}. I think this is because Set.insert is the underlying mechanism by which Lean interprets something like {a,b,c}.
  -/
  rfl
  /-
  Similarly, x ∈ {y} is shorthand for x = y. This, I think, is why rfl clears the goal.
  -/
  exact hb.right
  rw[mem_powerset_iff]
  rw[subset_iff]
  push_neg
  use a
  constructor
  left
  rfl
  exact ha.right

Conclusion ""
