import Game.Levels.RelationWorld.RelationWorldExamples.relation_example2

World "RelationWorldExamples"
Level 6

Title "Relation Example 3"

Introduction "One more level with composite practice. This one is much simpler."

/-- If $R$ and $S$ are reflexive relations on $u$, then $R ∘ S$ is also reflexive.-/
Statement {u : Type} (R S: Rel_on u) (hR: isReflexive R) (hS: isReflexive S) : isReflexive (R ∘ S) := by
  intro x
  obtain hR' := hR x
  obtain hS' := hS x
  exist x
  constructor
  exact hS'
  exact hR'


Conclusion "An even shorter name for this theorem is \"Composite of reflexive relations is reflexive\"."

/- Use these commands to add items to the game's inventory. -/
