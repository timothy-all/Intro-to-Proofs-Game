import Game.Levels.RelationWorld

World "RelationWorldExamples"
Level 4

Title "Relations"

Introduction "Let's prove that the subset statement in level 4 of Relation World is an equality if we assume `Ran(R) ⊆ Dom(S)`."

Statement {u v w : Type} (R: Rel u v) (S: Rel v w) (h: R.range ⊆ S.dom) : R.dom ⊆ (S ∘ R).dom := by
  intros x k
  obtain ⟨y, hy⟩ := k
  obtain hy2 : y ∈ R.range
  use x
  apply h at hy2
  obtain ⟨z,hz⟩ := hy2
  use z
  use y

Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
