import Game.Levels.ArgWorld.L06_arg

World "ArgWorld"
Level 7

Title "Proving a disjunction: Part 1"

Introduction "
### **Level 7**
"

set_option pp.parens true


Statement (P Q : Prop) (h : P) : P ∨ Q := by
  left
  exact h

Conclusion ""

NewTactic left
