import Game.Levels.SetWorld.L08_set

World "SetWorld"
Level 9

Title "Unions of families"

Introduction "
## **Level 7**
Let `F : Set (Set u)`. The **union** of all members of `F` is defined by:
```
⋃₀ F = { x | ∃ (t : Set (Set u)), t ∈ F ∧ x ∈ t}
```
So the membership proposition `x ∈ ⋃₀ F` means the same thing as `∃ (t : Set (Set u)), t ∈ F ∧ x ∈ t`.
"

Statement {u : Type} (A : Set u) (F : Set (Set u)) (h : A ∈ F) : A ⊆ ⋃₀ F := by
  intro a ha
  /- ⋃₀ F is sugar for SupSet F; the membership proposition x ∈ ⋃₀ F unpacks to ∃ (t : Set (Set u)), t ∈ F ∧ x ∈ t. -/
  use A
  --refine Exists.intro A ?_ -- this is more verbose, but I wanted to see more
  --refine ⟨h, ha⟩




Conclusion ""
