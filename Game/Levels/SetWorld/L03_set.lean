import Game.Levels.SetWorld.L02_set

World "SetWorld"
Level 3

Title "Set Intersection"

open Set

Introduction "
# **Level 3: Intersections**
![Venn diagram of intersection connective](images/venn_inter.png)
>
If `A B : Set u` then the set connective `∩` (intersection), illustrated above, is defined as follows:
```
A ∩ B = {x | x ∈ A ∧ x ∈ B}
```
This means that, definitionally, to say that `x ∈ A ∩ B` means the same thing as `x ∈ A ∧ x ∈ B`. 👉 To rewrite `x ∈ A ∩ B` as `x ∈ A ∧ x ∈ B` use
```
rw[mem_inter_iff] at h
```
"

/-- If $A ∈ A ∩ B$, then $a ∈ A$.-/
Statement {u : Type} (a : u) (A B : Set u) (h : a ∈ A ∩ B) : a ∈ A := by
  rw[mem_inter_iff] at h -- not even needed
  Hint "Almost done; we can clear this level with one more line."
  exact h.left


Conclusion "### **💡 Pro-tip**
We could have one-shotted this level with `exact h.left`. Lean knows that `A ∩ B` is definitionally a `∧` statement, so the `rw` step was unnecessary."

NewDefinition Set.mem_inter_iff
