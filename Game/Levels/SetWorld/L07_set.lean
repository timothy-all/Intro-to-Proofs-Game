import Game.Levels.SetWorld.L06_set

World "SetWorld"
Level 7

Title "Intersections of families"

Introduction "
# **Level 6: Family Intersection**
![Venn diagram of an intersection of a family](images/venn_finter.png)
>
Let `F : Set (Set u)`. This means that `F` is a *set of sets*, or as we say in class, a family of sets. The intersection of all members of `F`, illustrated above when `F = {A,B,C}`, is defined by:
```
⋂₀ F = { x | ∀ (t : Set (Set u)), t ∈ F → x ∈ t}
```
But first and foremost, our goal is a subset relation which we know is really just a universally quantified goal. So we should introduce some things ...
"

/-- The intersection of a family of sets is contained in any individual member of the family.-/
Statement {u : Type} (A : Set u) (F : Set (Set u)) (h : A ∈ F) : ⋂₀ F ⊆ A := by
  intro a ha
  /- ⋂₀ F is sugar for InfSet F; the membership proposition x ∈ ⋂₀ F unpacks to ∀ (t : Set (Set u)), t ∈ F → x ∈ t. -/
  Hint "Great. 👉 To rewrite `x ∈ ⋂₀ F` as `∀ (t : Set u), t ∈ F → x ∈ t` use
  ```
  rw[mem_finter_iff] at {ha}
  ```
  "
  rw[mem_finter_iff] at ha -- this is completely unnecessary but designed for consistency
  Hint "If we're clever, we can one-shot it from here."
  exact ha A h


Conclusion "### **💡 Pro-tip**
Lean knows that `a ∈ ⋂₀ F` is definitionally a universal statement, so the `rw` step was unnecessary in this proof."

NewDefinition mem_finter_iff
