import Game.Levels.SetWorld.L09_set

World "SetWorld"
Level 10

Title "Unions of indexed families"

Introduction "
# **Level 10: Unions of Indexed Families**
![Venn diagram of intersection of an indexed family](images/venn_iunion.png)
>
Let `A : I → Set u`. This means that `A` is a function from `I` (an indexing set) to `Set u`, sets in the universe `u`. Or as we say in class, an **indexed** family of sets. The union of all members of the indexed family (illustrated above where `I = {1,2,3}`) is defined by:
```
⋃ i, A i = { x | ∃ i, x ∈ A i}
```
But, as before, first and foremost our goal is a subset relation which we know is really just a universally quantified goal. Let's begin by introducing the appropriate stuff...
"

/-- Any individual member of an indexed family of sets is contained in the union of the indexed family.-/
Statement {u I: Type*} (A : I → Set u) (j : I) : A j ⊆ ⋃ i, A i  := by
  intro x hx
  Hint "Good. Now, the membership proposition in our goal `x ∈ ⋃ i, A i` means the same thing as `∃ i, x ∈ A i`. 👉 To rewrite `{hx}` in this form, try
  ```
  rw[mem_iunion_iff] at {hx}
  ```
  "
  rw[mem_iunion_iff]
  Hint "See how the goal is an existentially quantified statement over the indexing set `I` now? We need a witness."
  exist j
  exact hx



Conclusion "### **💡 Pro-tip**
The `rw` step was **necessary** here. This is because Lean sees `⋃ i, A i` as being definitionally equivalent to `⋃₀ F` for an appropriate family `F`. So we're once removed from the `∃` statement we might expect."

NewDefinition mem_iunion_iff
