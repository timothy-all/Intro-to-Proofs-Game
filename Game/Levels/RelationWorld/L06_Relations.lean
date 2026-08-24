import Game.Levels.RelationWorld.L05_Relations

World "RelationWorld"
Level 6

Title "Relations 4"

Introduction " ## **Level 6**

Let's see how to use some of the special relation definitions that go into partial orders and equivalence relations. Since these are relations on single sets, we have the new definition `Rel.on A` as a shorthand for `Rel A A`.
The names for our familiar definitions are `isReflexive`, `isSymmetric`, `isAntisymmetric`, and `isTransitive`. The definitions `isPartialOrder` and `isEquivalence` combine the relevant definitions. Check them out in your inventory.

Let's go through a few basic examples."

Statement {u : Type} (R: Rel_on u) : (Rel_id u).set ⊆ R.set ↔ isReflexive R := by
  constructor
  intro k y
  rw [Rel_id_set] at k
  obtain l: (y,y) ∈ R.set
  apply k
  exist y
  rfl
  exact l
  intro k y l
  rw [Rel_id_set] at l
  obtain ⟨a,ha⟩ := l
  rw [← ha]
  apply k


Conclusion "English proof?"

NewDefinition isReflexive isSymmetric isAntisymmetric isTransitive isPartialOrder isEquivalence
