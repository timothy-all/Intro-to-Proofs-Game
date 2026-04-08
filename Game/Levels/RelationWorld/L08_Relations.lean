import Game.Levels.RelationWorld.L07_Relations

World "RelationWorld"
Level 8

Title "Relations 6"

Introduction "Here is a standard transitive example."

Statement {u : Type} (R: Rel_on u) : (R ∘ R).set ⊆ R.set ↔ isTransitive R := by
  constructor
  intro h a b c k l
  obtain i : (a,c) ∈ (R ∘ R).set
  use b
  exact h i
  intro h x k
  rcases k with ⟨y,hy⟩
  exact h x.1 y x.2 hy.left hy.right


Conclusion "English proof?"

/- Use these commands to add items to the game's inventory. -/
