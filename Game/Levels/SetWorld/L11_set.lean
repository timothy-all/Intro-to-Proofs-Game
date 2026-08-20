import Game.Levels.SetWorld.L10_set

World "SetWorld"
Level 11

Title "The whole universe"

Introduction "
## **Level 9**
The **universal-set** denoted `Set.univ` is defined as follows:
```
univ = {x | True}
```
So the membership proposition `x ∈ Set.univ` means the same thing as `True`.
"
open Set


Statement {u : Type} (A : Set u) : A ∩ univ = A := by
  rw[set_eq_iff]
  intro x
  rw[mem_inter_iff]
  rw[mem_univ_iff_true]
  rw[And_true]

Conclusion ""

NewDefinition mem_univ_iff_true
