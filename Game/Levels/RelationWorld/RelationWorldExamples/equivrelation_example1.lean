import Game.Levels.RelationWorld.RelationWorldExamples.orderrelation_example2

World "RelationWorldExamples"
Level 11

Title "Equivalence Relation Example 1"

Introduction "If equivalence relations have the same family of equivalence classes, they're the same relation.

### **💡 Pro-tip**

Don't forget about some of our results from Relation World, such as `Equiv_class_has_rep`!"

Statement {u : Type*} (R S: Rel_on u) (eqR: isEquivalence R) (eqS: isEquivalence S) (h: equivClassFamily R = equivClassFamily S) : R = S := by
  apply Rel_double_inclusion
  apply Double_inclusion
  intro x hx
  obtain k : equivClass R x.1 ∈ equivClassFamily S
  rw[← h]
  exist x.1
  rfl
  obtain ⟨y,hy⟩ := k
  obtain hx1 : x.1 ∈ equivClass S y
  rw [hy]
  exact Equiv_class_has_rep R eqR x.1
  obtain hx2 : x.2 ∈ equivClass S y
  rw [hy]
  exact hx
  obtain hx1y : S x.1 y := eqS.symm hx1
  exact eqS.tran hx1y hx2

  intro x hx
  obtain k : equivClass S x.1 ∈ equivClassFamily R
  rw[h]
  exist x.1
  rfl
  obtain ⟨y,hy⟩ := k
  obtain hx1 : x.1 ∈ equivClass R y
  rw [hy]
  exact Equiv_class_has_rep S eqS x.1
  obtain hx2 : x.2 ∈ equivClass R y
  rw [hy]
  exact hx
  obtain hx1y : R x.1 y := eqR.symm hx1
  exact eqR.tran hx1y hx2

  Conclusion "If you're seeing this, good job! This is not an easy formalization!"
