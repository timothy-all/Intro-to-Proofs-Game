import Game.Levels.RelationWorld

World "RelationWorldExamples"
Level 5

Title "Relations"

Introduction "This level gives some good practice with composite relations."

Statement {u : Type} (R S: Rel_on u) (hR: isTransitive R) (hS: isTransitive S) (h: (S ∘ R).set ⊆ (R ∘ S).set) : isTransitive (R ∘ S) := by
  intro a b c kab kbc
  rcases kab with ⟨mid1,hmid1⟩
  rcases kbc with ⟨mid2,hmid2⟩
  obtain l1: (R ∘ S) mid1 mid2
  sorry
  sorry


Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/
