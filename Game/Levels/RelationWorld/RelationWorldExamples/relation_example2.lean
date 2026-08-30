import Game.Levels.RelationWorld.RelationWorldExamples.relation_example1

World "RelationWorldExamples"
Level 5

Title "Relations"

Introduction "This level gives some good practice with composite relations."

Statement {u : Type} (R S: Rel_on u) (hR: isTransitive R) (hS: isTransitive S) (h: (S ∘ R).pairs ⊆ (R ∘ S).pairs) : isTransitive (R ∘ S) := by
  intro a b c kab kbc
  obtain ⟨mid1,hmid1⟩ := kab
  obtain ⟨mid2,hmid2⟩ := kbc
  obtain l1: (mid1,mid2) ∈ (S ∘ R).pairs
  exist b
  constructor
  exact hmid1.right
  exact hmid2.left
  apply h at l1
  obtain ⟨mid3,hmid3⟩ := l1
  obtain ⟨hmid1l, hmid1r⟩ := hmid1
  obtain ⟨hmid2l, hmid2r⟩ := hmid2
  obtain ⟨hmid3l, hmid3r⟩ := hmid3
  obtain l2: S a mid3
  exact hS hmid1l hmid3l
  obtain l3: R mid3 c
  exact hR hmid3r hmid2r
  exist mid3
  refine ⟨l2,l3⟩


Conclusion "Proof in English?"

/- exist these commands to add items to the game's inventory. -/
