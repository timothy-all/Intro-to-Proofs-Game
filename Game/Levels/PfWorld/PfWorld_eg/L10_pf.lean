import Game.Levels.PfWorld.PfWorld_eg.L09_pf

World "PfWorld_eg"
Level 10

Title "Example 10"

Introduction "
### **Level 10**
"

Statement {u : Type*} (A B C : Set u) : C ⊆ A Δ B ↔ (C ⊆ A ∪ B ∧ (A ∩ B ∩ C = ∅)) := by
  constructor
  intro hC
  constructor
  intro c hc
  obtain ⟨hcA,hcB'⟩ | ⟨hcB,hcA'⟩ := hC hc
  left
  exact hcA
  right
  exact hcB
  rw[set_eq_iff]
  intro x
  constructor
  intro hx
  obtain this | that := hC hx.right
  exact this.right hx.left.right -- negated statements are weird
  exact that.right hx.left.left
  intro F
  contradiction
  intro ⟨h₁,h₂⟩ c hc
  by_cases ha : c ∈ A
  left
  refine ⟨ha,?_⟩
  by_contra! hb
  obtain F : c ∈ A ∩ B ∩ C := And.intro (And.intro ha hb) hc
  rw[h₂] at F
  exact F
  right
  refine ⟨?_,ha⟩
  obtain F | hb := h₁ hc
  contradiction
  exact hb


Conclusion ""
