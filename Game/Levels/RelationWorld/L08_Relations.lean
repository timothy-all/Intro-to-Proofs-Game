import Game.Levels.RelationWorld.L07_Relations

World "RelationWorld"
Level 8

Title "Relations 6"

Introduction " ## **Level 8**

Here is a standard transitive example."

Statement {u : Type} (R: Rel_on u) : (R ∘ R).set ⊆ R.set ↔ isTransitive R := by
  constructor
  intro h a b c k l
  obtain i : (a,c) ∈ (R ∘ R).set
  exist b
  refine ⟨k,l⟩
  exact h i
  intro h x k
  obtain ⟨y,hy⟩ := k
  exact h hy.left hy.right


Conclusion "English proof?"

/- Use these commands to add items to the game's inventory. -/
