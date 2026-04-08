import Game.Levels.SetWorld.L05_set

World "SetWorld"
Level 6

Title "DeMorgan : Compliment of a Union"

Introduction "
## **Level 6**
If `A : Set u` then **compliment** of `A` denoted `Aᶜ` is defined as follows:
```
Aᶜ  = { x | ¬ x ∈ A }
```
This means that, definitionally, to say that `x ∈ Aᶜ` means the same thing as `¬ x ∈ A`.
"

Statement {u : Type} (A B : Set u) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply Set.ext
  intro x
  rw[Set.mem_compl_iff]
  rw[Set.mem_union]
  rw[Not_or]
  rw[Set.mem_inter_iff]
  rw[Set.mem_compl_iff]
  rw[Set.mem_compl_iff]


Conclusion ""
