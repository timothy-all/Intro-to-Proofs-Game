import Game.Levels.RelationWorld.L06_Relations

World "RelationWorld"
Level 7

Title "Relations 5"

Introduction " ## **Level 7**

Here is a standard symmetric example."

Statement {u : Type} (R: Rel_on u) : R.inv.pairs ⊆ R.pairs ↔ isSymmetric R := by
  constructor
  intro h x a k
  obtain i : (a,x) ∈ R.inv.pairs
  exact k
  apply h at i
  exact i
  intro h x k
  apply h at k
  exact k


Conclusion "English proof?"
