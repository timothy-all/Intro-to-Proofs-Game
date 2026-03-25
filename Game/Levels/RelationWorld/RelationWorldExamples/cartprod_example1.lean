import Game.Levels.RelationWorld

World "RelationWorldExamples"
Level 1

Title "Cartesian products"

Introduction "Double inclusion exercise involving Cartesian products."



Statement (u v: Type) (A: Set u) (B C: Set v) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  apply Set.Subset.antisymm
  rw[Set.subset_def]
  intro x
  sorry
  sorry


Conclusion "As a proof in English, our steps here translate to:
Since `x ∉ A × B`, we know that it's not true that the first coordinate of `x` is in `A` and the second coordinate of `x` is in B.
unfinished"

/- Use these commands to add items to the game's inventory. -/

--DefinitionDoc Set.Prod as "×ˢ"

TheoremDoc mem_prod as "mem_prod"
TheoremDoc Set.Subset.antisymm as "double_inclusion"

--TheoremDoc Set.eq_of_subset_of_subset as "double_inclusion"

NewTactic rw rfl intro apply symm Or.inl obtain
NewTheorem mem_prod Not_and Set.Subset.antisymm
-- NewTheorem Nat.add_comm Nat.add_assoc
NewDefinition Set.Prod
