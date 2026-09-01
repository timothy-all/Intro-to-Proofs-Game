import Game.Levels.RelationWorld.RelationWorldExamples.orderrelation_example1

World "RelationWorldExamples"
Level 10

Title "Order Relations Example 2"

Introduction "Recall that, if `S` is a subset of `u`, `subsetOrder S` is the subset partial order on `S`.

In this exercise, you'll prove that the greatest lower bound of a family of sets `F` is `⋂F`. It might be a good idea to look back at your old Set World inventory items to figure out how to start..."

/-- If $F$ is a family of sets of elements of $u$, then the greatest lower bound of the subset partial order on $F$ is $⋂F$.-/
Statement {u : Type*} (F : Set (Set u)) : isInfimum (subsetOrder u) (⋂₀ F) F := by
  constructor
  intro A hA x hx
  exact hx A hA
  intro A hA x hx B hB
  obtain k : A ⊆ B := hA B hB
  exact k hx

Conclusion "This is an example of a proof where, in English, it's somewhat difficult to know what to say. The Lean guides us here!"
