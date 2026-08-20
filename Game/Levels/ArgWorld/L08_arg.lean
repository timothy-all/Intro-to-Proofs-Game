import Game.Levels.ArgWorld.L07_arg

World "ArgWorld"
Level 8

Title "Proving a disjunction: Part 2"

Introduction "
### **Level 8**
"

set_option pp.parens true


Statement (P Q : Prop) (h : Q) : P ∨ Q := by
  right
  exact h

Conclusion ""

NewTactic right
