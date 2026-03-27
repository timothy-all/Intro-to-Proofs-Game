import Game.Levels.RelationWorld

World "RelationWorldExamples"
Level 1

Title "Cartesian products"

Introduction "Double inclusion exercise involving Cartesian products.

Note: It is possible to prove this just using rewrites, but the intent is to get double inclusion practice. Start with `apply double_inclusion` to set up your double inclusion proof."



Statement (u v: Type) (A: Set u) (B C: Set v) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  apply Set.Subset.antisymm
  rw[Set.subset_def]
  intro x
  intro h
  rw [mem_diff,mem_prod,mem_prod,Not_and,And_comm (x.1 ∈ A), And_assoc,And_or_left,And_not_self,False_or,← And_assoc, And_comm (x.2 ∈ B), And_assoc,← mem_diff,← mem_prod]
  exact h
  intro x
  intro h
  rw [mem_diff,mem_prod,mem_prod,Not_and,And_comm (x.1 ∈ A), And_assoc,And_or_left,And_not_self,False_or,← And_assoc, And_comm (x.2 ∈ B), And_assoc,← mem_diff,← mem_prod] at h
  exact h


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
