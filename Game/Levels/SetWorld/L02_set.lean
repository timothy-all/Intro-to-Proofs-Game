import Game.Levels.SetWorld.L01_set

World "SetWorld"
Level 2

Title "Subset is transitive"

Introduction "
## **Level 2**
The **subset** relation is transitive. This means that if $A ⊆ B$ and $B ⊆ C$, then $A ⊆ C$. Let's prove this in Lean. Our goal is to prove `A ⊆ C`. Remember: this is just short-hand for:
```
∀ x, x ∈ A → x ∈ C
```
Let's `intro` a generic variable, say `a`, and the assumption that `a ∈ A`.
"

/-- The subset relation is transitive. -/
Statement Subseteq_trans {u : Type*} {A B C: Set u} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro a ha
  Hint "Perfect. We can clear the goal in one line if we're clever."
  exact h2 (h1 ha)


Conclusion ""
