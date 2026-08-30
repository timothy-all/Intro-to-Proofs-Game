import Game.Levels.SetWorld.L07_set

World "SetWorld"
Level 8

Title "Intersections of indexed families"

Introduction "
# **Level 8: Indexed intersections**
![Venn diagram of intersection of an index family](images/venn_iinter.png)
>
Let `A : I → Set u`. This means that `A` is a function from `I` (an indexing set) to `Set u`, sets in the universe `u`. Or as we say in class, an **indexed** family of sets. The intersection of all members of `A` (illustrated above where `I = {1,2,3}`) is defined by:
```
⋂ i, A i = { x | ∀ i, x ∈ A i}
```
But, as before, first and foremost our goal is a subset relation which we know is really just a universally quantified goal. Let's begin by introducing the appropriate stuff...
"

/-- The intersection of an indexed family of sets is contained in any individual member of the indexed family.-/
Statement {u I: Type*} (A : I → Set u) (j : I) : ⋂ i, A i ⊆ A j := by
  intro x hx
  Hint "Good. Now, the membership proposition in our goal `x ∈ ⋂ i, A i` means the same thing as `∀ i, x ∈ A i`. 👉 To rewrite `{hx}` in this form, try
  ```
  rw[mem_iinter_iff] at {hx}
  ```
  "
  rw[mem_iinter_iff] at hx
  Hint "See how the assumption `{hx}` is a universally quantified statement over the indexing set `I` now? We can clear this level with one more tactic call."
  exact hx j

Conclusion "### **💡 Pro-tip**
The `rw` step was **necessary** here. This is because Lean sees `⋂ i, A i` as being definitionally equivalent to `⋂₀ F` for an appropriate family `F`. So we're once removed from the `∀` statement we might expect."

NewDefinition mem_iinter_iff
