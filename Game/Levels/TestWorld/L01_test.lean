import Game.Metadata

World "TestWorld"
Level 1

Title "Test"

Introduction "
"

theorem test1 {α : Type} (A B C : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hxA
  exact h2 (h1 hxA)

Conclusion "
"
