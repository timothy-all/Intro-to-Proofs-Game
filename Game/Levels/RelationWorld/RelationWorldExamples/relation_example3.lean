import Game.Levels.RelationWorld.RelationWorldExamples.relation_example2

World "RelationWorldExamples"
Level 6

Title "Relations"

Introduction "One more level with composite practice. This one is much simpler."

Statement {u : Type} (R S: Rel_on u) (hR: isReflexive R) (hS: isReflexive S) : isReflexive (R ∘ S) := by
  intro x
  obtain hR' := hR x
  obtain hS' := hS x
  exist x
  constructor
  exact hS'
  exact hR'


Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
