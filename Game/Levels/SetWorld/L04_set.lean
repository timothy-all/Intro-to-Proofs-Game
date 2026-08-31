import Game.Levels.SetWorld.L03_set

World "SetWorld"
Level 4

Title "Set Union"

Introduction "
# **Level 4: Unions**
![Venn diagram of union connective](images/venn_union.png)
>
If `A B : Set u` then the set connective `∪` (union) is defined as follows:
```
A ∪ B = {x | x ∈ A ∨ x ∈ B}
```
This means that, definitionally, to say that `x ∈ A ∪ B` means the same thing as `x ∈ A v x ∈ B`. 👉 To rewrite `x ∈ A ∪ B` as `x ∈ A ∨ x ∈ B` use
```
rw[mem_union_iff]
```
"
/-- If $a ∈ A$, then $a ∈ A ∪ B$..-/
Statement {u : Type*} (a : u) (A B : Set u) (h : a ∈ A) : a ∈ A ∪ B := by
  rw[mem_union_iff]
  Hint "So we have to prove an or-statement. At the moment, our only approach is a direct one. Do we want to try to prove the *left* or *right* side of this or-statement?"
  left
  Hint "Almost done."
  exact h


Conclusion "### **💡 Pro-tip**
Lean knows that `A ∪ B` is definitionally a `∨` statement, so the `rw` step was unnecessary."

NewDefinition mem_union_iff
