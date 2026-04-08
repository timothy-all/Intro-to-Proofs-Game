import Game.Levels.SetWorld.L01_set

World "SetWorld"
Level 2

Title "Subset Relation"

Introduction "
## **Level 2**

"

Statement {u : Type} (A B C: Set u) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro a ha
  exact h2 (h1 ha)


Conclusion ""
