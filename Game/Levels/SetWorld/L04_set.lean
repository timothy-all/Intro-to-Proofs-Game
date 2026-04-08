import Game.Levels.SetWorld.L03_set

World "SetWorld"
Level 4

Title "Set Union"

Introduction "
## **Level 4**
If `A B : Set u` then the set connective `∪` (union) is defined as follows:
```
A ∩ B = {x | x ∈ A ∨ x ∈ B}
```
This means that, definitionally, to say that `x ∈ A ∪ B` means the same thing as `x ∈ A v x ∈ B`.
"

Statement {u : Type} (a : u) (A B : Set u) (h : a ∈ A) : a ∈ A ∪ B := by
  left
  exact h


Conclusion ""
