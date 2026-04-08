import Game.Levels.RelationWorld.L06_Relations

World "RelationWorld"
Level 7

Title "Relations 5"

Introduction "Here is a standard symmetric example."

Statement {u : Type} (R: Rel_on u) : R.inv.set ⊆ R.set ↔ isSymmetric R := by
  constructor
  intro h x a k
  obtain i : (a,x) ∈ R.inv.set
  exact k
  apply h at i
  exact i
  intro h x k
  apply h at k
  exact k


Conclusion "English proof?"

/- Use these commands to add items to the game's inventory. -/
