import Game.Levels.SetWorld.L11_set

World "SetWorld"
Level 12

Title "The whole universe"

Introduction "
# **Level 12**
The **universal-set** denoted `univ` is defined as follows:
```
univ = {x | True}
```
Our current goal is a set equality; let's rewrite that goal using `set_eq_iff`.
"
open Set


Statement {u : Type} (A : Set u) : A ∩ univ = A := by
  rw[set_eq_iff]
  Hint "Our goal now is a universally quantified statement. Let's introduce a generic variable."
  intro x
  Hint "The left-hand side of the logical equivalence in our goal is a membership of an intersection. Let's rewrite that."
  rw[mem_inter_iff]
  Hint "The membership proposition `x ∈ univ` means the same thing as `True`. 👉 To rewrite `x ∈ univ` in this form, try
  ```
  rw[mem_univ_iff_true]
  ```
  "
  rw[mem_univ_iff_true]
  Hint "Almost done."
  rw[And_true]

Conclusion ""

NewDefinition mem_univ_iff_true
