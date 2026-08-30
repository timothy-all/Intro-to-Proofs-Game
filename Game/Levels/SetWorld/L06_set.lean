import Game.Levels.SetWorld.L05_set

World "SetWorld"
Level 6

Title "DeMorgan : Compliment of a Union"

open Set

Introduction "
# **Level 6: Equality & Compliments**
If `A B : Set u`, then we say `A = B` to mean that
```
set_eq_iff : ∀ x, x ∈ A ↔ x ∈ B
```
👉 To rewrite `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ` in this way use
```
rw[set_eq_iff]
```
"

open Set

/-- The compliment of a union is the intersection of the individual compliments.-/
Statement {u : Type*} (A B : Set u) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  rw[set_eq_iff] -- or we could just use Set.ext_iff
  Hint "See how our goal is now a universal statement? Let's introduce a generic variable to reckon with the universal quantifier"
  intro x
  Hint "Great. Now, if `A : Set u` then **compliment** of `A` denoted `Aᶜ` is defined as follows:
  ```
  Aᶜ  = \{ x | ¬ x ∈ A }
  ```
  This means that, definitionally, to say that `x ∈ Aᶜ` means the same thing as `¬ x ∈ A`. 👉 Try
  ```
  rw[mem_compl_iff]
  ```
  "
  rw[mem_compl_iff]
  Hint "Lean writes `x ∉ ...` as short-hand for `¬ x ∈ ...`. So let's try
  ```
  rw[mem_union_iff]
  ```
  "
  rw[mem_union_iff]
  Hint "The left-hand side of our goal is the negation of an `∨` statement. Try to finish this level off on your own."
  rw[mem_inter_iff]
  rw[mem_compl_iff]
  rw[mem_compl_iff]
  rw[Not_or]

Conclusion "One can similarly show that `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`."

NewDefinition set_eq_iff Set.mem_compl_iff mem_union_iff
