import Game.Levels.ArgWorld.L03_arg

World "ArgWorld"
Level 4

Title "Conjunctive Simplification"

Introduction "
# **Level 4**
This valid argument is sometimes called the law of **Conjunctive Simplification**.
"

set_option pp.parens true

/-- This valid argument is known as *Conjunctive Simplification*.-/
Statement (P Q: Prop) (h : P ∧ Q) : P := by
  Hint "We simply need to destructure the assumption `h : P ∧ Q`. 👉 Try:
  ```
  obtain hP : = h.left
  ```
  This will create a new assumption, namely `hP : P`.
  "
  obtain hP := h.left
  exact hP


Conclusion "### **💡 Pro-tip**
We've learned that if `h : P ∧ Q`, then `h.left` is a proof of `P`. 🤔 Can you take a wild guess at what `h.right` proves? What if `h : P ∧ (Q ∧ R)` ... what is `h.right.left` a proof of?"
