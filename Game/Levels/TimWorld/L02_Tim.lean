import Game.Levels.TimWorld.L01_Tim

World "TimWorld"
Level 2

Title "Test"

Introduction "
### **🤔 Level 2?**
"

/--
Suppose $P$ and $Q$ are propositions. If $P ∧ Q$ is true, then $Q$ is true.
-/
TheoremDoc and_right as "and_right"

Statement and_right (P Q : Prop) : (P ∧ Q) → Q := by
  intro h
  exact h.right



Conclusion ""
