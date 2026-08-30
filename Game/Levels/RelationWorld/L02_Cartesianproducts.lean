import Game.Levels.RelationWorld.L01_Cartesianproducts

World "RelationWorld"
Level 2

Title "Cartesian products"

Introduction " ## **Level 2: Cartesian products**

The previous level suggests that we can conclude that an element fails to be in a Cartesian product as long as at least one coordinate fails to be in the required set; specifically, in terms of this statement, the first coordinate.
Let's prove it."



/-- If $x ∉ A$, it's not possible for $(x,y) ∈ A ×ˢ B$, regardless of what $y$ is.-/
Statement Fst_not_mem_not_mem_prod {u v: Type*} (A: Set u) (B: Set v) (x : u) (y: v) (h: x ∉ A) : (x,y) ∉ (A ×ˢ B) := by
  Hint "Unpack what it means to be a member of a Cartesian product, then you'll need to use known facts about `or` statements."
  rw [mem_prod_iff,Not_and]
  left
  exact h


Conclusion "A similar statement is true using the second Cartesian product coordinate. Can you formulate what it should be?"

NewTheorem Not_mem_prod
