import Game.Levels.QuantifierWorld
import Game.Levels.SetWorld.set_docs
import Game.Levels.SetWorld.Metadata_setworld

World "SetWorld"
Level 1

Title "Subset Relation"

Introduction "
## **Level 1**
If `A B : Set u`, then the **subset** relation `A ⊆ B` is defined as follows:
```
∀ {x}, x ∈ A → x ∈ B
```
The curly braces around the first `x` indicate that Lean considers this argument to be *implicit*. This means that Lean will infer what `x` is from the argument `x ∈ A`.
"

Statement {u : Type} (a : u) (A B : Set u) (h1 : A ⊆ B) (h2 : a ∈ A) : a ∈ B := by
  exact h1 h2


Conclusion ""
