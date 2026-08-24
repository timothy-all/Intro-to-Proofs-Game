import Game.Levels.RelationWorld.RelationWorldExamples.orderrelation_example2

World "RelationWorldExamples"
Level 11

Title "Equivalence Relations"

Introduction "If equivalence relations have the same family of equivalence classes, they're the same relation."

Statement {u : Type*} (R S: Rel_on u) (eqR: isEquivalence R) (eqS: isEquivalence S) (h: equivClassFamily R = equivClassFamily S) : R = S := by
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  obtain k : equivClass R x.1 ∈ equivClassFamily S := by
    rw[← h]
    use x.1
  obtain ⟨y,hy⟩ := k
  obtain hx1 : x.1 ∈ equivClass S y := by
    rw [hy]
    exact Equiv_class_has_rep R eqR x.1
  obtain hx2 : x.2 ∈ equivClass S y := by
    rw [hy]
    exact hx
  obtain hx1y : S x.1 y := eqS.symm hx1
  exact eqS.tran hx1y hx2

  intro x hx
  obtain k : equivClass S x.1 ∈ equivClassFamily R := by
    rw[h]
    use x.1
  obtain ⟨y,hy⟩ := k
  obtain hx1 : x.1 ∈ equivClass R y := by
    rw [hy]
    exact Equiv_class_has_rep S eqS x.1
  obtain hx2 : x.2 ∈ equivClass R y := by
    rw [hy]
    exact hx
  obtain hx1y : R x.1 y := eqR.symm hx1
  exact eqR.tran hx1y hx2

  Conclusion "Proof in English?"
