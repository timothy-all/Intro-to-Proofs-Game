import Game.Levels.SetWorld.L10_set

World "SetWorld"
Level 11

Title "Empty Set"

Introduction "
# **Level 11**
The **empty-set** denoted `∅` is defined as follows:
```
∅ = {x | False}
```
Our goal is an equality of sets. 👉 So let's get started with
```
rw[set_eq_iff]
```
"
open Set

Statement {u : Type} (A : Set u) : A ∩ ∅ = ∅ := by
  rw[set_eq_iff]
  Hint "Great. Now we have a universally quantified statement as our goal. Let's introduce a generic variable."
  intro x
  Hint "Super. We now need to prove this logical equivalence. We might start by rewriting what it means to be a member of an intersection..."
  rw[mem_inter_iff]
  Hint "Preem. Now, the membership proposition `x ∈ ∅` means the same thing as `False`. 👉 To rewrite `x ∈ ∅` in this form try
  ```
  rw[mem_empty_iff_false]
  ```
  "
  rw[mem_empty_iff_false]
  Hint "We now have `⊢ _ ∧ False ↔ False` as our goal. There's a theorem from **Logical Equivalence World** that will clear the goal for us."
  rw[And_false] -- introduce And_false in EquivWorld. Done


Conclusion ""

NewDefinition Set.mem_empty_iff_false
