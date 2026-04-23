import Game.Levels.RelationWorld.L05_Relations

World "RelationWorld"
Level 6

Title "Relations 4"

Introduction "Let's see how to use some of the special relation definitions that go into partial orders and equivalence relations. Since these are relations on single sets, we have the new definition `Rel.on A` as a shorthand for `Rel A A`.
The names for our familiar definitions are `isReflexive`, `isSymmetric`, `isAntisymmetric`, and `isTransitive`. The definitions `isPartialOrder` and `isEquivalence` combine the relevant definitions. Check them out in your inventory.

Let's go through a few basic examples."

Statement {u : Type} (R: Rel_on u) : (Rel_id u).set ⊆ R.set ↔ isReflexive R := by
  constructor
  intro k y
  rw [Rel_id_set] at k
  obtain l: (y,y) ∈ R.set
  apply k
  use y
  exact l
  intro k y l
  rw [Rel_id_set] at l
  obtain ⟨a,ha⟩ := l
  rw [← ha]
  apply k


Conclusion "English proof?"

/- Use these commands to add items to the game's inventory. -/

/-- `Rel_on A` is the same thing as `Rel A A`. Shorthand for a relation on a single set. -/
DefinitionDoc Rel_on as "REL: Rel_on"

/-- Makes a relation `R` reflexive. -/
DefinitionDoc isReflexive as "REL: isReflexive"

/-- Makes a relation `R` symmetric. -/
DefinitionDoc isSymmetric as "REL: isSymmetric"

/-- Makes a relation `R` anti-symmetric. -/
DefinitionDoc isAntisymmetric as "REL: isAntiymmetric"

/-- Makes a relation `R` transitive. -/
DefinitionDoc isTransitive as "REL: isTransitive"

/-- Makes a relation `R` an equivalence relation. -/
DefinitionDoc isEquivalence as "REL: isEquivalence"
