import Game.Metadata

World "RelationWorld"
Level 2

Title "Cartesian products"

Introduction "The previous level suggests that we can conclude that an element fails to be in a Cartesian product as long as at least one coordinate fails to be in the required set.
Let's prove it."



Statement fst_not_mem_not_mem_prod (u v: Type) (A: Set u) (B: Set v) (x : u) (y: v) (h: x ∉ A) : (x,y) ∉ (A ×ˢ B) := by
  Hint "Use the previous level to simplify, then you'll need to use known facts about `or` statements."
  rw [mem_prod,Not_and]
  apply Or.intro_left
  exact h


Conclusion "Include a proof in English"

/- Use these commands to add items to the game's inventory. -/

--DefinitionDoc Set.Prod as "×ˢ"

TheoremDoc mem_prod as "mem_prod"

NewTactic intro apply symm Or.inl obtain
NewTheorem mem_prod Not_and
-- NewTheorem Nat.add_comm Nat.add_assoc
NewDefinition Set.Prod
