import Game.Metadata

World "TestWorld"
Level 1

Title "Test"

Introduction "
"

theorem test1 {u : Type} (A B C : Set u) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hxA
  exact h2 (h1 hxA)

theorem test2 {u : Type} (A B : Set u) (p : u → Prop) (q : u → Prop) (h : ∀ x : u, p x → q x) : {x | p x} ⊆ {x | q x} := by
  intro a ha
  exact h a ha

Conclusion "
"
