import Game.Levels.SetWorld.L02_set

World "SetWorld"
Level 3

Title "Set Intersection"

Introduction "
## **Level 3**
If `A B : Set u` then the set connective `∩` (intersection) is defined as follows:
```
A ∩ B = {x | x ∈ A ∧ x ∈ B}
```
This means that, definitionally, to say that `x ∈ A ∩ B` means the same thing as `x ∈ A ∧ x ∈ B`.
"

Statement {u : Type} (a : u) (A B : Set u) (h1 : a ∈ A ∩ B) : a ∈ A := by
  --rw[Set.mem_inter_iff] at h1 -- not even needed
  exact h1.left


Conclusion ""
