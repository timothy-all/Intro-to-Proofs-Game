import Game.Levels.RelationWorld.RelationWorldExamples.orderrelation_example1

World "RelationWorldExamples"
Level 10

Title "Order Relations"

Introduction "Recall that, is `S` is a subset of `u`, `subsetOrder S` is the subset partial order on `S`.

In this exercise, you'll prove that the greatest lower bound of a  family of sets `F` is `⋂F`."

Statement {u : Type*} (F : Set (Set u)) : isInfimum (subsetOrder u) (⋂₀ F) F := by
  sorry

Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
