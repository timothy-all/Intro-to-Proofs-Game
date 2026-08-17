import Game.Levels.SetWorld.L10_set

World "SetWorld"
Level 11

Title "The whole universe"

Introduction "
## **Level 9**
The **universal-set** denoted `Set.univ` is defined as follows:
```
Set.univ = {x | True}
```
So the membership proposition `x ∈ Set.univ` means the same thing as `True`.
"


Statement {u : Type} (A : Set u) : A ∩ Set.univ = A := by
  apply Set.ext
  intro x
  rw[Set.mem_inter_iff]
  rw[mem_univ_iff_true]
  rw[And_true]

Conclusion ""
