import Game.Levels.RelationWorld.L05_Relations

World "RelationWorld"
Level 6

Title "Relations 4"

Introduction " ## **Level 6**

Let's see how to use some of the special relation definitions that go into partial orders and equivalence relations. The names for our familiar definitions are `isReflexive`, `isSymmetric`, `isAntisymmetric`, and `isTransitive`. The definitions `isPartialOrder` and `isEquivalence` combine the relevant definitions. Check them out in your inventory.

Let's go through a few basic examples."

Statement {u : Type} (R: Rel_on u) : (Rel_id u).pairs ⊆ R.pairs ↔ isReflexive R := by
  constructor
  intro k y
  rw [Rel_id_pairs] at k
  obtain l: (y,y) ∈ R.pairs
  apply k
  exist y
  rfl
  exact l
  intro k y l
  rw [Rel_id_pairs] at l
  obtain ⟨a,ha⟩ := l
  rw [← ha]
  apply k


Conclusion "English proof?"

NewDefinition isReflexive isSymmetric isAntisymmetric isTransitive isPartialOrder isEquivalence
