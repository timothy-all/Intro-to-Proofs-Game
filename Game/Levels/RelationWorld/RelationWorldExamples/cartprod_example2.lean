import Game.Levels.RelationWorld.RelationWorldExamples.cartprod_example1

World "RelationWorldExamples"
Level 2

Title "Cartesian product Example 2"

Introduction "Double inclusion exercise involving Cartesian products.

🔍 Check your inventory for a new theorem: `Snd_not_mem_not_mem_prod.` This is similar to the theorem proven in level 2 of RelationWorld, just using the second coordinate instead of the first. Both of these are useful in this level."


/-- If $A, B, C, D$ are sets, then $(A × B) \setminus (C × D) = (A × (B \setminus D)) ∪ ((A \setminus C) × B).$ -/
Statement (u v: Type) (A C: Set u) (B D: Set v) : (A ×ˢ B) \ (C ×ˢ D) = (A ×ˢ (B \ D)) ∪ ((A \ C) ×ˢ B) := by
  apply Double_inclusion
  intro x
  intro h
  rw[mem_diff_iff,
    mem_prod_iff,
    mem_prod_iff,
    Not_and,
    And_or_left] at h
  obtain h1 | h2 := h
  rw[And_assoc, And_comm (x.2 ∈ B), ← And_assoc, ← mem_diff_iff,← mem_prod_iff] at h1
  rw[mem_union_iff]
  right
  exact h1
  rw[And_assoc, ← mem_diff_iff,← mem_prod_iff] at h2
  left
  exact h2

  intro x
  intro h
  rw[mem_union_iff] at h
  obtain h1 | h2 := h
  rw[mem_prod_iff, mem_diff_iff,← And_assoc, ← mem_prod_iff] at h1
  rw[mem_diff_iff]
  constructor
  exact h1.left
  obtain ⟨h1l,h1r⟩ := h1
  apply Snd_not_mem_not_mem_prod
  exact h1r
  rw[mem_prod_iff, mem_diff_iff,And_assoc, And_comm (x.1 ∉ C),← And_assoc, ← mem_prod_iff] at h2
  rw[mem_diff_iff]
  refine ⟨h2.left,?_⟩
  apply Fst_not_mem_not_mem_prod
  exact h2.right


Conclusion "Compare your work with a proof in English. Which steps do you think need to be mentioned carefully, and which do you think readers will infer automatically?"

NewTheorem Snd_not_mem_not_mem_prod
