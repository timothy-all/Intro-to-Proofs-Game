import Game.Levels.SetWorld.L07_set

World "SetWorld"
Level 8

Title "Intersections of indexed families"

Introduction "
## **Level 8**
Let `A : I → Set u`. This means that `A` is a function from `I` (an indexing set) to `Set u`, sets in the universe `u`. Or as we say in class, an **indexed** family of sets. The intersection of all members of `A` is defined by:
```
⋂ i, A i = { x | ∀ i, x ∈ A i}
```
So the membership proposition `x ∈ ⋂ i, A i` means the same thing as `∀ i, x ∈ A i`.
"

Statement {u I: Type*} (A : I → Set u) (j : I) : ⋂ i, A i ⊆ A j := by
  intro x hx
  rw[mem_iinter] at hx
  exact hx j



Conclusion ""
