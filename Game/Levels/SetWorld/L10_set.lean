import Game.Levels.SetWorld.L09_set

World "SetWorld"
Level 10

Title "Empty Set"

Introduction "
## **Level 10**
The **empty-set** denoted `∅` is defined as follows:
```
∅ = {x | False}
```
So the membership proposition `x ∈ ∅` means the same thing as `False`.
"
open Set

Statement {u : Type} (A : Set u) : A ∩ ∅ = ∅ := by
  rw[set_eq_iff]
  intro x
  rw[mem_inter_iff]
  rw[mem_empty_iff_false]
  rw[And_false] -- introduce And_false in EquivWorld


Conclusion ""

NewDefinition Set.mem_empty_iff_false
