import Game.Metadata

World "TimWorld"
Level 1

Title "Test"

Introduction "
### **🤔 Level 1?**

"

/--
Suppose $P$ and $Q$ are propositions. If $P ∧ Q$ is true, then $P$ is true.
-/
TheoremDoc and_left as "and_left"

Statement and_left (P Q : Prop) : (P ∧ Q) → P := by
  intro h
  exact h.left



Conclusion ""

NewTactic intro exact
