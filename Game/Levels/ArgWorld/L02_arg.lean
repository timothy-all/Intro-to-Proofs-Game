import Game.Levels.ArgWorld.L01_arg

World "ArgWorld"
Level 2

Title "Modus Tolens"

Introduction "
### **Level 2**
"


Statement (P Q : Prop) (hPQ : P → Q) (hnQ : ¬ Q) : ¬ P := by
  rw[contrapositive] at hPQ
  exact hPQ hnQ


Conclusion ""
