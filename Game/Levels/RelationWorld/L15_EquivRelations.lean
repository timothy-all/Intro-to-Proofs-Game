import Game.Levels.RelationWorld.L14_EquivRelations
open Set

World "RelationWorld"
Level 15

Title "Equivalence Relations"

Introduction "Next, toward our goal of proving that `equivClassFamily R` is a partition, let's prove that every element of `u` belongs to some equivalence class."


Statement {u : Type*} (R: Rel_on u) (eq: isEquivalence R) : ⋃₀ (equivClassFamily R) = univ := by
  Hint "This is an equality of sets, so as usual, `apply double_inclusion`."
  apply double_inclusion
  Hint "Every set is a subset of the universe, so this is trivial & Lean knows it - `exact subset_univ (⋃₀ (equivClassFamily R))` closes the goal."
  exact subset_univ (⋃₀ (equivClassFamily R))
  Hint "This is the direction where we have to say something - `intro a ha` to grab an arbitrary element of the universe."
  intro a ha
  Hint "We have to find an equivalence class containing `a`. What should it be?"
  use (equivClass R a)
  constructor
  use a
  exact Equiv_class_has_rep R eq a


Conclusion "English proof?"
