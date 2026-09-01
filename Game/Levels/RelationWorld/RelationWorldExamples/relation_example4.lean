import Game.Levels.RelationWorld.RelationWorldExamples.relation_example3

World "RelationWorldExamples"
Level 7

Title "Relation Example 4"

Introduction "Practice with inverses."

/-- If $R$ and $S$ are relations from $u$ to $v$ such that $R ⊆ S$, then $R^{-1} ⊆ S^{-1}$.-/
Statement {u v : Type} (R S: Rel u v) (h: R.pairs ⊆ S.pairs) : R.inv.pairs ⊆ S.inv.pairs := by
  intro x k
  obtain h': (x.2,x.1) ∈ R.pairs
  exact k
  exact h h'

Conclusion "Inverses are super nice in the Lean game - this level can be solved with as few as 4 commands! How many did your solution use?"
