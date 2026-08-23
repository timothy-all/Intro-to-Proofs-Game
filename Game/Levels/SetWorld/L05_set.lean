import Game.Levels.SetWorld.L04_set

World "SetWorld"
Level 5

Title "Set Difference"

Introduction "
# **Level 4: Difference**
| | | |
|---|:---:|---|
| | ![Venn diagram of the difference connective](images/venn_diff.png) | |
>
If `A B : Set u` then the set connective `\\` (set-difference) is defined as follows:
```
A \\ B = {x | x ∈ A ∧ ¬ x ∈ B}
```
This means that, definitionally, to say that `x ∈ A \\ B` means the same thing as `x ∈ A ∧ ¬ x ∈ B`.  👉 To rewrite `h : x ∈ A \\ B` as `h : x ∈ A ∧ x ∉ B` use
```
rw[mem_diff_iff] at h
```
"

Statement {u : Type} (a : u) (A B : Set u) (h : a ∈ A \ B) : a ∉ B := by
  rw[mem_diff_iff] at h
  Hint "See how `h` is now the more verbose `h : x ∈ A ∧ x ∉ B`? Almost done."
  exact h.right


Conclusion "### **💡 Pro-tip**
We could have one-shotted this level with `exact h.right`. Lean knows that `A \\ B` is definitionally a `∧` statement, so the `rw` step was unnecessary."

NewDefinition mem_diff_iff
