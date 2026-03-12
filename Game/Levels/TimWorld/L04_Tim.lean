import Game.Levels.TimWorld.L03_Tim

World "TimWorld"
Level 4

Title "Test"

Introduction "
### **🤔 Level 4?**
"

/--
Suppose $P$ and $Q$ are propositions. If $P ∧ Q$ is true, then $Q$ is true.
-/
TheoremDoc or_right as "or_right"

Statement or_right (P Q : Prop) : Q → (P ∨ Q) := by
  intro hQ
  right
  exact hQ



Conclusion ""

NewTactic right
