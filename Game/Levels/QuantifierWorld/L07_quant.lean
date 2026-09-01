import Game.Levels.QuantifierWorld.L06_quant

World "QuantifierWorld"
Level 7

Title "Forall distributes over and"

Introduction "
# **Level 7**
The `∀` quantifier distributes over `∧` statements. Logically, this makes sense given that we know that the `∧` connective is associative and commutative, and what is `∀` but a giant `∧` connective. We have a universal quantifier to reckon with, so let's start with
```
intro x
```
"

/-- To say `(∀ x, P x) ∧ (∀ x, Q x)` means the same thing as `∀ x, P x ∧ Q x`.-/
Statement {u : Type*} {P Q : u → Prop} (h: (∀ x, P x) ∧ (∀ x, Q x)) : ∀ x, P x ∧ Q x := by
  intro x
  Hint "Great. We can clear this with one line now."
  exact And.intro (h.left x) (h.right x)

Conclusion "The converse of this is also true. From here on out the logical equivalence
```
(∀ x, P x) ∧ (∀ x, Q x) ↔ ∀ x, P x ∧ Q x
```
is available and called `Forall_and`.
### **🥳 Congrats!**
You've beaten Quantifier World! As always, Quantifier Examples World contains a lot of practice levels. The next new world is Set World."

NewTheorem Forall_and
