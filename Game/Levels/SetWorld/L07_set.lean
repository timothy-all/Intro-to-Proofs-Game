import Game.Levels.SetWorld.L05_set

World "SetWorld"
Level 6

Title "Intersections of families"

Introduction "
## **Level 6**
Let `F : Set (Set u)`. This means that `F` is a *set of sets*, or as we say in class, a family of sets. The intersection of all members of `F` is defined by:
```
⋂₀ F = { x | ∀ (t : Set (Set u)), t ∈ F → x ∈ t}
```
To rewrite `x ∈ ⋂₀ F` as `∀ (t : Set u), t ∈ F → x ∈ t` we use `mem_finter`.
"

Statement {u : Type} (A : Set u) (F : Set (Set u)) (h : A ∈ F) : ⋂₀ F ⊆ A := by
  intro a ha
  /- ⋂₀ F is sugar for InfSet F; the membership proposition x ∈ ⋂₀ F unpacks to ∀ (t : Set (Set u)), t ∈ F → x ∈ t. -/
  rw[mem_finter] at ha -- this is completely unnecessary but designed for consistency
  exact ha A h


Conclusion ""
