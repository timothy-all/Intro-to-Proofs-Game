import Game.Levels.SetWorld.L09_set

World "SetWorld"
Level 10

Title "Unions of indexed families"

Introduction "
# **Level 10: Unions of Indexed Families**
| | | |
|---|:---:|---|
| | ![Venn diagram of intersection of an indexed family](images/venn_iinter.png) | |
>
Let `A : I → Set u`. This means that `A` is a function from `I` (an indexing set) to `Set u`, sets in the universe `u`. Or as we say in class, an **indexed** family of sets. The intersection of all members of `A` (illustrated above where `I = {1,2,3}`) is defined by:
```
⋂ i, A i = { x | ∀ i, x ∈ A i}
```
But, as before, first and foremost our goal is a subset relation which we know is really just a universally quantified goal. Let's begin by introducing the appropriate stuff...
"

Statement {u I: Type*} (A : I → Set u) (j : I) : A j ⊆ ⋃ i, A i  := by
  intro x hx
  Hint "Good. Now, the membership proposition in our goal `x ∈ ⋂ i, A i` means the same thing as `∀ i, x ∈ A i`. 👉 To rewrite `{hx}` in this form, try
  ```
  rw[mem_iinter_iff] at {hx}
  ```
  "
  rw[mem_iunion_iff]
  Hint "See how the goal is an existentially quantified statement over the indexing set `I` now? We need a witness."
  use j



Conclusion ""

NewDefinition mem_iunion_iff
