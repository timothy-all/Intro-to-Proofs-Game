import Game.Levels.SetWorld.L09_set

World "SetWorld"
Level 10

Title "Empty Set"

Introduction "
## **Level 9**
The **empty-set** denoted `∅` is defined as follows:
```
∅ = {x | False}
```
So the membership proposition `x ∈ ∅` means the same thing as `False`.
"


Statement {u : Type} (A : Set u) : A ∩ ∅ = ∅ := by
  apply Set.ext
  intro x
  rw[Set.mem_inter_iff]
  rw[Set.mem_empty_iff_false]
  rw[And_false]


Conclusion ""
