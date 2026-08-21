import Game.Levels.ArgWorld.L07_arg

World "ArgWorld"
Level 8

Title "Proving a disjunction: Part 2"

Introduction "
# **Level 8**
This level is a natural companion to the previous one.
"

set_option pp.parens true

/-- This valid argument is known as *Disjunctive Amplification*.-/
Statement (P Q : Prop) (h : Q) : P ∨ Q := by
  right
  exact h

Conclusion "### **🥳 Congrats!**
You beat Argument World! Next up Argument Examples World."
