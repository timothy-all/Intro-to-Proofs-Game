import Game.Levels.RelationWorld.RelationWorldExamples.relation_example1

World "RelationWorldExamples"
Level 5

Title "Relations"

Introduction "This level gives some good practice with composite relations."

Statement {u : Type} (R S: Rel_on u) (hR: isTransitive R) (hS: isTransitive S) (h: (S ∘ R).set ⊆ (R ∘ S).set) : isTransitive (R ∘ S) := by
  intro a b c kab kbc
  rcases kab with ⟨mid1,hmid1⟩
  rcases kbc with ⟨mid2,hmid2⟩
  obtain l1: (mid1,mid2) ∈ (S ∘ R).set
  use b
  constructor
  exact hmid1.right
  exact hmid2.left
  apply h at l1
  rcases l1 with ⟨mid3,hmid3⟩
  rcases hmid1 with ⟨hmid1l, hmid1r⟩
  rcases hmid2 with ⟨hmid2l, hmid2r⟩
  rcases hmid3 with ⟨hmid3l, hmid3r⟩
  obtain l2: S a mid3
  exact hS hmid1l hmid3l
  obtain l3: R mid3 c
  exact hR hmid3r hmid2r
  use mid3


Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
