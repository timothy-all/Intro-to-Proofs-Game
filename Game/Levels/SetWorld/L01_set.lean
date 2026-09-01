import Game.Levels.QuantifierWorld
import Game.Levels.SetWorld.set_docs
import Game.Levels.SetWorld.Metadata_setworld

World "SetWorld"
Level 1

Title "Subset Relation"

Introduction "
# **Level 1: Subsets**
![Venn diagram of subset relation](images/venn_subset.png)
>
If `A B : Set u`, then the **subset** relation `A ⊆ B`, illustrated above, is defined as follows:
```
subset_iff : ∀ {x}, x ∈ A → x ∈ B
```
### **⌨ Typesetting tip**
In order to write the symbol `⊆` use `\\subseteq`. To write the symbol `∈` use `\\in`.
>
The curly braces around the first `x` in `subset_iff` indicate that Lean considers this argument to be *implicit*. This means that Lean will infer what `x` is from the argument `x ∈ A`. 👉 To start, try
```
rw[subset_iff] at hAB
```
"

open Set

/-- If $A$ is contained in $B$ and $a ∈ A$, then $a ∈ B$. -/
Statement {u : Type} (a : u) (A B : Set u) (hAB : A ⊆ B) (ha : a ∈ A) : a ∈ B := by
  rw[subset_iff] at hAB
  Hint "See how the hypothesis `hAB` is now rewritten according to the definition? 👉 Now try
  ```
  obtain h := hAB ha
  ```
  "
  obtain h := hAB ha
  Hint "**Note:** we didn't have to specify the value `a`! This was inferred from `ha : a ∈ A`. Nearly done."
  exact h

Conclusion "### **💡 Pro-tip**
We could have one-shotted this level with `exact hAB ha`. Lean knows that `A ⊆ B` is definitionally a `→` statement, so the `rw` step was unnecessary.
>
Implicit arguments like the one used in `subset_iff` make our lives a bit easier. For example, if
```
subset_iff : ∀ x, x ∈ A → x ∈ B
```
so that the variable `x` was *explicit*, then we'd need to use `obtain h := hAB a ha` instead of the shorter version above."


NewDefinition subset_iff
