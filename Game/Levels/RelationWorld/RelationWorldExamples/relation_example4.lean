import Game.Levels.RelationWorld.RelationWorldExamples.relation_example3

World "RelationWorldExamples"
Level 7

Title "Relations"

Introduction "Practice with inverses."

Statement {u v : Type} (R S: Rel u v) (h: R.pairs ⊆ S.pairs) : R.inv.pairs ⊆ S.inv.pairs := by
  intro x k
  obtain h': (x.2,x.1) ∈ R.pairs
  exact k
  exact h h'

Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
