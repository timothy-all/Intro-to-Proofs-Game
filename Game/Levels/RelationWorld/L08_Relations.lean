import Game.Metadata

World "RelationWorld"
Level 8

Title "Relations 6"

Introduction "Here is a standard transitive example."

Statement {u : Type} (R: Rel_on u) : (R ∘ R).set ⊆ R.set ↔ isTransitive R := by
  constructor
  intro h a b c k l
  obtain i : (a,c) ∈ (R ∘ R).set
  use b
  apply h at i
  exact i
  intro h x k
  obtain l : ∃ y, (R x.1 y) ∧ (R y x.2)
  apply k
  obtain ⟨y,hy⟩ := l
  apply h x.1 y x.2 --Suffices to fulfill hypotheses for transitive with x.1, y, x.2
  exact hy.left
  exact hy.right


Conclusion "English proof?"

/- Use these commands to add items to the game's inventory. -/
