import Game.Levels.ArgWorld.L03_arg

World "ArgWorld"
Level 4

Title "Conjunctive Simplification"

Introduction "
### **Level 4**
This valid argument is sometimes called the law of **Conjunctive Simplification**.
"

set_option pp.parens true



Statement (P Q: Prop) (h : P ∧ Q) : P := by
  exact h.left


Conclusion ""
