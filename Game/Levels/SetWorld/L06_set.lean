import Game.Levels.SetWorld.L05_set

World "SetWorld"
Level 6

Title "DeMorgan : Compliment of a Union"

open Set

Introduction "
## **Level 6**
If `A : Set u` then **compliment** of `A` denoted `Aᶜ` is defined as follows:
```
Aᶜ  = { x | ¬ x ∈ A }
```
This means that, definitionally, to say that `x ∈ Aᶜ` means the same thing as `¬ x ∈ A`.
"

open Set

Statement {u : Type} (A B : Set u) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  rw[set_eq_iff] -- or we could just use Set.ext_iff
  intro x
  rw[mem_compl_iff]
  rw[mem_union_iff]
  rw[Not_or]
  rw[mem_inter_iff]
  rw[mem_compl_iff]
  rw[mem_compl_iff]


Conclusion ""

NewDefinition set_eq_iff Set.mem_compl_iff mem_union_iff
