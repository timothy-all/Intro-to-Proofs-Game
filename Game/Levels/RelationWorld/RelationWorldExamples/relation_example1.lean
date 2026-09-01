import Game.Levels.RelationWorld.RelationWorldExamples.cartprod_example3

World "RelationWorldExamples"
Level 4

Title "Relation Example 1"

Introduction "Let's prove that the subset statement in level 4 of Relation World is an equality if we assume `Ran(R) ⊆ Dom(S)`."

/-- If $R$ is a relation from $u$ to $v$ and $S$ is a relation from $v$ to $w$ such that range$(R) ⊆ $ domain$(S)$, then domain$(R) ⊆ $ domain$(S ∘ R)$.-/
Statement {u v w : Type} (R: Rel u v) (S: Rel v w) (h: R.range ⊆ S.dom) : R.dom ⊆ (S ∘ R).dom := by
  intro x k
  obtain ⟨y, hy⟩ := k
  obtain hy2 : y ∈ R.range
  exist x
  exact hy
  apply h at hy2
  obtain ⟨z,hz⟩ := hy2
  exist z
  exist y
  constructor
  exact hy
  exact hz

Conclusion "Needing extra assumptions for converses to be true is common in math. Sometimes finding suitable conditions for a converse to be true can turn into a full-blown research project!"

/- exist these commands to add items to the game's inventory. -/
