import Game.Levels.SetWorld.L11_set

World "SetWorld"
Level 12

Title "Symmetric Difference"

Introduction "
# **Level 12: Symmetric Difference**
![Venn diagram of the difference connective](images/venn_symm.png)
>
If `A B : Set u` then the set connective `Δ` (symmetric difference) is defined as follows:
```
A Δ B = (A \\ B) ∪ (B \\ A)
```
This means that, definitionally, to say that `x ∈ A Δ B` means the same thing as `x ∈ A \\ B ∪ B \\ A`.
>
But first, we have a set equality to reckon with. 👉 Let's start with
```
rw[set_eq_iff]
```
"

set_option pp.parens true
open Set

/-- The symmetric difference of a set with itself is the empty set.-/
Statement Symm_diff_self {u : Type*} {A: Set u} : A Δ A = ∅ := by
  rw[set_eq_iff]
  Hint "Now let's `intro` a generic variable."
  intro x
  Hint "Let's unravel the membership of `x ∈ A Δ A`. 👉 We can do this with
  ```
  rw[mem_symm_diff_iff]
  ```
  "
  rw[mem_symm_diff_iff]
  Hint "👉 Now let's unravel the union with
  ```
  rw[mem_union_iff]
  ```
  "
  rw[mem_union_iff]
  Hint "👉 Finally, let's unravel the set-difference with
  ```
  rw[mem_diff_iff]
  ```
  "
  rw[mem_diff_iff]
  Hint "What logical equivalences will help us out here? Try to get our goal into the shape `⊢ False ↔ (x ∈ ∅)`."
  rw[And_not_self]
  rw[Or_false]
  Hint "Great. We're almost home."
  rw[mem_empty_iff_false]

Conclusion "This theorem will be helpful again in the future."

NewDefinition mem_symm_diff_iff

/- Save this for proof by contradiction example
Statement {u : Type} (A B : Set u) : A ⊆ B ↔ A \ B = ∅ := by

Save this for proof of or
Statement {u : Type} (A B C: Set u) : (A ∪ B) \ (C \ A) ⊆ A ∪ (B \ C) := by
-/
