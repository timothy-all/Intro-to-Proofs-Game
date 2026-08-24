import Game.Levels.RelationWorld.RelationWorldExamples.relation_example3

World "RelationWorldExamples"
Level 7

Title "Relations"

Introduction "Practice with inverses."

Statement {u v : Type} (R S: Rel u v) (h: R.set ⊆ S.set) : R.inv.set ⊆ S.inv.set := by
  intro x k
  obtain h': (x.2,x.1) ∈ R.set := by
    exact k
  exact h h'

Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
