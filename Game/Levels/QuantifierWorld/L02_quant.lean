import Game.Levels.QuantifierWorld.L01_quant

World "QuantifierWorld"
Level 2

Title "Universal Generalization"

Introduction "
## **Level 2**
In this level, we have a universal statement as a *goal*. To prove such a statement, we use the principle known as **Universal Generalization**. Specifically, to prove a universally quantified statement like `∀ x, Q x` we should prove that `Q x` is true for a **generically** chosen element of the universe of discourse. How do we tell Lean to choose a generic element of `u`?
### **❯ The `intro` tactic ... again**
If the `intro` tactic is called against a universally quantified goal, like `⊢ ∀ x, Q x`, it will initialize a generic element of `u` and change the goal to `⊢ Q ⟨id⟩` where `⟨id⟩` is whatever identifier we use with `intro`. In our case, 👉 try:
```
intro a
```
"

/-- We use *Universal Generalization* to prove this statement.-/
Statement {u : Type} (a : u) (P Q : u → Prop) (hPQ : ∀ x, P x → Q x) (hP : ∀ x, P x) : ∀ x, Q x := by
  intro a
  Hint "Notice that `a : u` (a generic element of type `u`) and our goal is to prove `Q a`? See if you can't finish this level off on your own."
  exact hPQ a (hP a)

Conclusion "🔧 The `intro` tactic can not only introduce hypotheses as assumptions, but (as we've seen here) can also introduce generic elements of universally quantified goals. In terms of translating Lean into a human-readable proof, it makes sense to translate a statement like `intro a` in this proof into *Let $a$ be a generic element.*"
