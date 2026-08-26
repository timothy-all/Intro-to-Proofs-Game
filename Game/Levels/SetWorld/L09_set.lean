import Game.Levels.SetWorld.L08_set

World "SetWorld"
Level 9

Title "Unions of families"

Introduction "
# **Level 9: Unions of Families**
| | | |
|---|:---:|---|
| | ![Venn diagram of union of a family of sets](images/venn_funion.png) | |
>
Let `F : Set (Set u)`. The **union** of all members of `F` is defined by:
```
⋃₀ F = { x | ∃ (t : Set (Set u)), t ∈ F ∧ x ∈ t}
```
But first and foremost, our goal is a subset relation. So we should begin, like you do, by introducing the appropriate material.
"

Statement {u : Type} (A : Set u) (F : Set (Set u)) (h : A ∈ F) : A ⊆ ⋃₀ F := by
  intro a ha
  Hint "The membership proposition `{a} ∈ ⋃₀ F` means the same thing as `∃ (t : Set (Set u)), t ∈ F ∧ {a} ∈ t`. 👉 To rewrite the goal in this form in this form, try
  ```
  rw[mem_funion_iff]
  ```
  "
  rw[mem_funion_iff]
  /- ⋃₀ F is sugar for SupSet F; the membership proposition x ∈ ⋃₀ F unpacks to ∃ (t : Set (Set u)), t ∈ F ∧ x ∈ t. -/
  Hint "Great. Now we have an existential goal. We need a witness..."
  exist A
  exact And.intro h ha
  --refine ⟨A,?_⟩
  --exact And.intro h ha



Conclusion ""

NewDefinition mem_funion_iff
