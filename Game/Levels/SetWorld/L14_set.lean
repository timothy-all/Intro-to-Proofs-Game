import Game.Levels.SetWorld.L13_set

World "SetWorld"
Level 14

Title "The whole universe"

Introduction "
# **Level 14**
The **universal-set** denoted `univ` is defined as follows:
```
univ = {x | True}
```
Our current goal is a subset relation; let's introduce the appropriate stuff.
"
open Set



/-- Every set `A` is a subset of `univ`.-/
Statement Subset_univ {u : Type*} (A : Set u) : A ⊆ univ := by
  intro a ha
  Hint "The membership proposition `{a} ∈ univ` means the same thing as `True`. 👉 To rewrite `{a} ∈ univ` in this form, try
  ```
  rw[mem_univ_iff_true]
  ```
  "
  rw[mem_univ_iff_true]
  Hint "***Great***. Now, is `True` true? You bet! In fact, `True` is so true that Lean has a theorem that says `trivial : True`. 👉 So we can close our goal with
  ```
  exact trivial
  ```
  "
  exact trivial

Conclusion ""

NewDefinition mem_univ_iff_true
NewTheorem trivial
