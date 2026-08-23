import Game.Levels.QuantifierWorld
import Game.Levels.SetWorld.set_docs
import Game.Levels.SetWorld.Metadata_setworld

World "SetWorld"
Level 1

Title "Subset Relation"

Introduction "
# **Level 1: Subsets**
| | | |
|---|:---:|---|
| | ![Venn diagram of subset relation](images/venn_subset.png) | |
>
If `A B : Set u`, then the **subset** relation `A ⊆ B`, illustrated above, is defined as follows:
```
∀ {x}, x ∈ A → x ∈ B
```
The curly braces around the first `x` indicate that Lean considers this argument to be *implicit*. This means that Lean will infer what `x` is from the argument `x ∈ A`. 👉 Try
```
rw[subset_iff] at h₁
```
"

open Set


Statement {u : Type} (a : u) (A B : Set u) (h₁ : A ⊆ B) (h₂ : a ∈ A) : a ∈ B := by
  rw[subset_iff] at h₁
  Hint "See how the hypothesis `h₁` is now rewritten according to the definition? Now try
  ```
  obtain h₃ := h₁ h₂
  ```
  **Note:** we didn't have to specify the value `a`! This was inferred from `h₁ : a ∈ A`.
  "
  obtain h₃ := h₁ h₂
  Hint "Nearly done."
  exact h₃

Conclusion "### **💡 Pro-tip**
We could have one-shotted this level with `exact h₁ h₂`. Lean knows that `A ⊆ B` is definitionally a `→` statement, so the `rw` step was unnecessary.
>
Implicit arguments like the one used in `subset_iff` make our lives a bit easier. For example, if
```
subset_iff : ∀ x, x ∈ A → x ∈ B
```
so that the variable `x` was *explicit*, then we'd need to use `obtain h₃ := h₁ a h₂` instead of the shorter version above."


NewDefinition subset_iff
