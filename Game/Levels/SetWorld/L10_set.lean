import Game.Levels.SetWorld.L08_set

World "SetWorld"
Level 9

Title "The whole universe"

Introduction "
## **Level 9**
The **universal-set** denoted `Set.univ` is defined as follows:
```
Set.univ = {x | True}
```
So the membership proposition `x ∈ Set.univ` means the same thing as `True`.
"

/- for metadata-/
theorem Set.mem_univ_iff_true {u : Type} (a : u) : a ∈ Set.univ ↔ True := by
  simp


Statement {u : Type} (A : Set u) : A ∩ Set.univ = A := by
  apply Set.ext
  intro x
  rw[Set.mem_inter_iff]
  rw[Set.mem_univ_iff_true]
  rw[And_true]

Conclusion ""
