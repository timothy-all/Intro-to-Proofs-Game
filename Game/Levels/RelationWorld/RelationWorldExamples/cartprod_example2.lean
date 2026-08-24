import Game.Levels.RelationWorld.RelationWorldExamples.cartprod_example1

World "RelationWorldExamples"
Level 2

Title "Cartesian products"

Introduction "Double inclusion exercise involving Cartesian products.

Check your inventory for a new theorem: `Snd_not_mem_not_mem_prod.` This is similar to the theorem proven in level 2 of RelationWorld, just using the second coordinate instead of the first. Both of these are useful in this level."



Statement (u v: Type) (A C: Set u) (B D: Set v) : (A ×ˢ B) \ (C ×ˢ D) = (A ×ˢ (B \ D)) ∪ ((A \ C) ×ˢ B) := by
  apply double_inclusion
  intro x
  intro h
  rw[Set.mem_diff,Mem_prod,Mem_prod,Not_and,And_or_left] at h
  cases h
  rw[And_assoc, And_comm (x.2 ∈ B), ← And_assoc, ← Set.mem_diff,← Mem_prod] at h_1
  rw[mem_union_iff]
  apply Or.intro_right
  exact h_1
  rw[And_assoc, ← Set.mem_diff,← Mem_prod] at h_1
  apply Or.intro_left
  exact h_1

  intro x
  intro h
  rw[mem_union_iff] at h
  cases h
  rw[Mem_prod, Set.mem_diff,← And_assoc, ← Mem_prod] at h_1
  rw[Set.mem_diff]
  constructor
  exact h_1.left
  apply And.right at h_1
  apply Snd_not_mem_not_mem_prod
  exact h_1
  rw[Mem_prod, Set.mem_diff,And_assoc, And_comm (x.1 ∉ C),← And_assoc, ← Mem_prod] at h_1
  rw[Set.mem_diff]
  constructor
  exact h_1.left
  apply And.right at h_1
  apply Fst_not_mem_not_mem_prod
  exact h_1


Conclusion "Proof in English?"

NewTheorem Snd_not_mem_not_mem_prod
