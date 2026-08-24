import Game.Levels.RelationWorld.L01_Cartesianproducts

World "RelationWorld"
Level 2

Title "Cartesian products"

Introduction " ## **Level 2**

The previous level suggests that we can conclude that an element fails to be in a Cartesian product as long as at least one coordinate fails to be in the required set.
Let's prove it."




Statement Fst_not_mem_not_mem_prod {u v: Type*} (A: Set u) (B: Set v) (x : u) (y: v) (h: x ∉ A) : (x,y) ∉ (A ×ˢ B) := by
  Hint "Use the previous level to simplify, then you'll need to use known facts about `or` statements."
  rw [Mem_prod,Not_and]
  apply Or.intro_left
  exact h


Conclusion "Include a proof in English"

NewTheorem Not_mem_prod
