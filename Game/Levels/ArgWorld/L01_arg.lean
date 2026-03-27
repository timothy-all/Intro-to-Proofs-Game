import Game.Levels.EquivWorld

World "ArgWorld"
Level 1

Title "Modus Ponens"

Introduction "
### **Level 1**
Lean natively is aware of the valid argument known as **modus ponens**. In fact, Lean has a funny way of interpreting...
### **Implications as functions**

"

/--
Exact doc
-/
TacticDoc exact

Statement (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

Conclusion ""

NewTactic exact
