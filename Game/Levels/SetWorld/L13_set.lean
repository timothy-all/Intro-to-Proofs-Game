import Game.Levels.SetWorld.L12_set

World "SetWorld"
Level 13

Title "Nonempty Sets"

Introduction "
# **Level 13**
A set `A` is **nonempty**, denoted in Lean with the *dot* notation `A.Nonempty`, means precisely the following:
```
A.Nonempty ↔ ∃ x, x ∈ A
```
Our goal in this level is an implication, so let's introduce the hypothesis...
"
open Set

/-- If $A$ is nonempty and $A$ is contained in $B$, then $B$ is nonempty. -/
Statement {u : Type*} (A B: Set u) (h : A.Nonempty) :  A ⊆ B → B.Nonempty :=  by
  intro hAB
  Hint "Great. Our hypothesis `h : A.Nonempty` is truly an existential statement. Let's grab a witness to that existential statement with `obtain`."
  obtain ⟨x,hx⟩ := h
  Hint "Our goal `⊢ B.Nonempty` is an existential statement. In order to see this existential statement explicitly, 👉 try
  ```
  rw[Set.Nonempty]
  ```
  "
  rw[Set.Nonempty]
  Hint "See how our goal is now a `∃` statement? We need to supply a witness..."
  exist x
  Hint "Perfect. Now our goal is `⊢ {x} ∈ B`. If we're clever, we can clear this with one more line. "
  exact hAB hx


Conclusion "### **💡 Pro-tip**
Lean knows that `A.Nonempty` is definitionally the same as `∃ x, x ∈ A`. So the `rw[Set.Nonempty]` step of our proof could be omitted."

NewDefinition Set.Nonempty
