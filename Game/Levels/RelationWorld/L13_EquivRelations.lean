import Game.Levels.RelationWorld.L12_EquivRelations

World "RelationWorld"
Level 13

Title "Equivalence Relations"

Introduction "Another important and basic fact about equivalence relations is the fact that they're nonempty; in particular, `equivClass R a` always contains `a`. Let's prove this so we can use it in future levels."

/-- This is the proof that `a ∈ equivClass R a`. --/
TheoremDoc Equiv_class_has_rep as "REL: Equiv_class_has_rep"


Statement Equiv_class_has_rep {u : Type*} (R: Rel_on u) (eq: isEquivalence R) (a : u)
 : a ∈ equivClass R a := by
  Hint "The goal is simply to show `R a a`. Which equivalence relation property tells us this?"
  exact eq.refl a


Conclusion "English proof?"
