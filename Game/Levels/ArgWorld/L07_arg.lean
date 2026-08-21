import Game.Levels.ArgWorld.L06_arg

World "ArgWorld"
Level 7

Title "Proving a disjunction: Part 1"

Introduction "
# **Level 7**
Proving a disjunction can be tricky and we'll develop strategies to tackle these kinds of goals later on. That being said, sometimes it's easy! Like in this level here. In order to tell Lean that we intend to directly prove the *left* side of this disjunction we need the tactic...
### **❯ The `left` and `right` tactics**
If our goal is of the form `⊢ P ∨ Q`, then the tactic `left` will change our goal to `⊢ P`. Similarly, the `right` tactic will change our goal to `⊢ Q`. 👉 In our case here, try
```
left
```
"

set_option pp.parens true

/-- This valid argument is known as *Disjunctive Amplification*.-/
Statement (P Q : Prop) (h : P) : P ∨ Q := by
  left
  Hint "One more line ought to clear this level..."
  exact h

Conclusion "There are more indirect ways to clear disjunctive goals. We'll tackle these in Proof Strategies World."

NewTactic left right
