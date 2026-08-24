import Game.Levels.RelationWorld.RelationWorldExamples.cartprod_example3

World "RelationWorldExamples"
Level 4

Title "Relations"

Introduction "Let's prove that the subset statement in level 4 of Relation World is an equality if we assume `Ran(R) ⊆ Dom(S)`."

Statement {u v w : Type} (R: Rel u v) (S: Rel v w) (h: R.range ⊆ S.dom) : R.dom ⊆ (S ∘ R).dom := by
  intro x k
  obtain ⟨y, hy⟩ := k
  obtain hy2 : y ∈ R.range
  use x
  exact hy
  apply h at hy2
  obtain ⟨z,hz⟩ := hy2
  use z
  use y
  constructor
  exact hy
  exact hz

Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
