import Game.Levels.SetWorld.L04_set

World "SetWorld"
Level 5

Title "Set Difference"

Introduction "
## **Level 4**
If `A B : Set u` then the set connective `\\` (set-difference) is defined as follows:
```
A \\ B = {x | x ∈ A ∧ ¬ x ∈ B}
```
This means that, definitionally, to say that `x ∈ A \\ B` means the same thing as `x ∈ A ∧ ¬ x ∈ B`.
"

Statement {u : Type} (a : u) (A B : Set u) (h : a ∈ A \ B) : a ∉ B := by
  exact h.right


Conclusion ""
