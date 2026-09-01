import Game.Levels.RelationWorld.RelationWorldExamples.relation_example4

World "RelationWorldExamples"
Level 8

Title "Relation Example 5"

Introduction "This exercise concerns the union of two relations. Since relations in the Intro Proofs Game use types, not sets, we have to be a bit careful about what this means.

In short, `(Rel_union R S) u v` is true when either `R u v` or `S u v`. Try the problem below, and 🔍 check your inventory for more information on `Rel_union`."

/-- If $R$ and $S$ are relations from $u$ to $v$, then $(R ∪ S)^{-1} = R^{-1} ∪ S^{-1}$.-/
Statement {u v : Type} (R S: Rel u v) : (Rel_union R S).inv = Rel_union R.inv S.inv  := by
  apply Rel_double_inclusion
  apply Double_inclusion
  intro x h
  obtain hP | hQ := h
  left
  exact hP
  right
  exact hQ
  intro x h
  obtain hP | hQ := h
  left
  exact hP
  right
  exact hQ

Conclusion "Unions of relations might seem like abstract nonsense, but they're used extensively in geometry when constructing functions on complicated objects!"

NewDefinition Rel_union
