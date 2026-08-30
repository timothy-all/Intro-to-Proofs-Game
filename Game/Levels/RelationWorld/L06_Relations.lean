import Game.Levels.RelationWorld.L05_Relations

World "RelationWorld"
Level 6

Title "Relations 4"

Introduction " ## **Level 6: A reflexive example**

Let's see how to use some of the special relation definitions that go into partial orders and equivalence relations. The names for our familiar definitions are `isReflexive`, `isSymmetric`, `isAntisymmetric`, and `isTransitive`. The definitions `isPartialOrder` and `isEquivalence` combine the relevant definitions. 🔍 Check them out in your inventory.

Let's go through a few basic examples."

/-- The identity relation is a subset of `R` if and only if `R` is reflexive. -/
Statement {u : Type} (R: Rel_on u) : (Rel_id u).pairs ⊆ R.pairs ↔ isReflexive R := by
  Hint "We're proving a biconditional statement here! 👉 Remember that this can be unpacked using `constructor`."
  constructor
  Hint "👉 Let's `intro k y`, then use our new Theorem from the last level to help see what `k` means: `rw [Rel_id_pairs] at k`."
  intro k y
  rw [Rel_id_pairs] at k
  Hint "Our goal is `R y y`, but what we know is about `R.pairs`, which is a bit awkward. One way around this is to use `obtain` to prove things about pairs instead of `R` directly. 👉 So let's `obtain l : (y,y) ∈ R.pairs`."
  obtain l: (y,y) ∈ R.pairs
  Hint "👉 `k` tells us it suffices to show that `(y,y)` is in the set shown in set-builder notation there, so `apply k`."
  apply k
  Hint "You know which element to give to satisfy this existence goal - don't overthink it!"
  exist y
  rfl
  exact l
  intro k y l
  rw [Rel_id_pairs] at l
  obtain ⟨a,ha⟩ := l
  rw [← ha]
  apply k


Conclusion "Let's continue on with some more examples involving equivalence relation properties."

NewDefinition isReflexive isSymmetric isAntisymmetric isTransitive isPartialOrder isEquivalence
