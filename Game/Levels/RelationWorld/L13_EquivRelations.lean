import Game.Levels.RelationWorld.L12_EquivRelations

World "RelationWorld"
Level 13

Title "Equivalence Relations"

Introduction "Another important and basic fact about equivalence classes is the fact that equivalence classes are independent of representative; that is, if `b ∈ equivClass R a`, then `equivclass R a = equivClass R b`. Let's prove this."




Statement Equiv_class_rep_ind {u : Type*} (R: Rel_on u) (eq: isEquivalence R) (a b: u) (h: b ∈ equivClass R a) : equivClass R a = equivClass R b := by
  Hint "Equivalence classes are sets! Let's prove this using double inclusion: `apply double_inclusion` then unpack the forall goal with `intro x hx`."
  apply double_inclusion
  intro x hx
  Hint "The goal amounts to proving `R b x`. We know `h : R a b` and `hx : R a x`. Use equivalence relation properties to take it from here!"
  obtain hba : R b a := eq.symm h
  exact eq.tran hba hx
  intro x hx
  exact eq.tran h hx

Conclusion "English proof?"


NewTheorem Equiv_class_has_rep
