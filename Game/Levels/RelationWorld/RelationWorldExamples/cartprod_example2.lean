import Game.Levels.RelationWorld.RelationWorldExamples.cartprod_example1

World "RelationWorldExamples"
Level 2

Title "Cartesian products"

Introduction "Double inclusion exercise involving Cartesian products.

Note: It is possible to prove this just using rewrites, but the intent is to get double inclusion practice. Start with `apply double_inclusion` to set up your double inclusion proof."



Statement (u v: Type) (A C: Set u) (B D: Set v) : (A ×ˢ B) \ (C ×ˢ D) = (A ×ˢ (B \ D)) ∪ ((A \ C) ×ˢ B) := by
  apply double_inclusion
  rw[subset_def]
  intro x
  intro h
  rw[Set.mem_diff,mem_prod,mem_prod,Not_and,And_or_left] at h
  cases h
  rw[And_assoc, And_comm (x.2 ∈ B), ← And_assoc, ← Set.mem_diff,← mem_prod] at h_1
  rw[mem_union]
  apply Or.intro_right
  exact h_1
  rw[And_assoc, ← Set.mem_diff,← mem_prod] at h_1
  apply Or.intro_left
  exact h_1

  rw[subset_def]
  intro x
  intro h
  rw[mem_union] at h
  cases h
  rw[mem_prod, Set.mem_diff,← And_assoc, ← mem_prod] at h_1
  rw[Set.mem_diff]
  constructor
  exact h_1.left
  apply And.right at h_1
  apply snd_not_mem_not_mem_prod
  exact h_1
  rw[mem_prod, Set.mem_diff,And_assoc, And_comm (x.1 ∉ C),← And_assoc, ← mem_prod] at h_1
  rw[Set.mem_diff]
  constructor
  exact h_1.left
  apply And.right at h_1
  apply fst_not_mem_not_mem_prod
  exact h_1


Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/

--DefinitionDoc Set.Prod as "×ˢ"

TheoremDoc mem_prod as "mem_prod"
TheoremDoc Set.Subset.antisymm as "double_inclusion"

--TheoremDoc Set.eq_of_subset_of_subset as "double_inclusion"

--NewTactic intro apply symm Or.inl obtain
NewTheorem mem_prod Set.Subset.antisymm
-- NewTheorem Nat.add_comm Nat.add_assoc
NewDefinition Set.Prod
