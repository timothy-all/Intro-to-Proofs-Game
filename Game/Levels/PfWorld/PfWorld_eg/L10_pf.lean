import Game.Levels.PfWorld.PfWorld_eg.L09_pf

World "PfWorld_eg"
Level 10

Title "Example 10"

Introduction "
### **Level 10**
"

Statement {u : Type*} (A B C : Set u) : C ⊆ symmDiff A B ↔ (C ⊆ A ∪ B ∧ (A ∩ B ∩ C = ∅ )) := by
  constructor
  intro hC
  constructor
  intro c hc
  obtain hc' := hC hc
  rcases hc' with ⟨hcA,hcB'⟩ | ⟨hcB,hcA'⟩
  left
  exact hcA
  right
  exact hcB
  rw[Set.eq_empty_iff_forall_notMem]
  intro x
  by_contra! F
  obtain F' := hC F.right
  rcases F' with ⟨hxA,hxB'⟩ | ⟨hxB,hxA'⟩
  exact hxB' F.left.right
  exact hxA' F.left.left
  intro ⟨hC,h⟩
  intro c hc
  obtain hc' := hC hc
  rcases hc' with hcA | hcB
  left
  refine ⟨hcA,?_⟩
  by_contra!
  obtain that : c ∈ A ∩ B ∩ C := And.intro (And.intro hcA this) hc
  rw[h] at that
  contradiction
  right
  refine ⟨hcB,?_⟩
  by_contra!
  obtain that : c ∈ A ∩ B ∩ C := And.intro (And.intro this hcB) hc
  rw[h] at that
  contradiction

Conclusion ""
