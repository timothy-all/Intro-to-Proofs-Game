import Game.Levels.QuantifierWorld.L04_quant
import Mathlib.Tactic.Push

World "QuantifierWorld"
Level 5

Title "Universal Quantifiers"

Introduction "
# **Level 5**
A negated `∀`-statement turns into an `∃`-statement and vice versa. This follows (essentially) from DeMorgan's law (remember: `∀` statements are like gigantic `∧`-statements). There is a tactic that will **push negatives** through quantified statements. Conveniently that tactic is called ...
### **❯ The `push_neg` tactic**
The tactic `push_neg` will push negations through the target. In our case, 👉 try:
```
push_neg at h
```
"

Statement {u : Type} (P : u → Prop) (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  push_neg at h
  Hint "See how `h` is now the hypothesis `h : ∃ x, ¬ P x`? We're almost done."
  exact h

Conclusion "### **💡 Pro-tip**
The `push_neg` tactic will push negations through logical connectives too. But be careful! For example, if `h : ¬ (P ∧ Q)`, then `push_neg at h` produces
```
h : P → ¬ Q
```
which *is* logically equivalent to `¬ P ∨ ¬ Q` but perhaps you would have expected the latter. Lean prefers the former due its preference for currying.
"

NewTactic push_neg
