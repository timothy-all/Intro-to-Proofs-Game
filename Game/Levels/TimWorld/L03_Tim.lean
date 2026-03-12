import Game.Levels.TimWorld.L02_Tim

World "TimWorld"
Level 3

Title "Test"

Introduction "
### **🤔 Level 3?**
"

/--
Suppose $P$ and $Q$ are propositions. If $P$ is true, then $P ∨ Q$ is true.
-/
TheoremDoc or_left as "or_left"

Statement or_left (P Q : Prop) : P → (P ∨ Q) := by
  intro hP
  left
  exact hP



Conclusion ""

NewTactic left
