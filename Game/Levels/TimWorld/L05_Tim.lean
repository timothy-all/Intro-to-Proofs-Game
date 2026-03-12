import Game.Levels.TimWorld.L04_Tim

World "TimWorld"
Level 5

Title "Test"

Introduction "
### **🤔 Level 5?**
Implications as functions.
"

/--
Suppose $P$ and $Q$ are propositions. If $P$ is true and $P → Q$ is true, then $Q$ is true.
-/
TheoremDoc modus_ponens as "modus_ponens"

Statement modus_ponens (P Q : Prop) : (P ∧ (P → Q)) → Q := by
  intro h
  exact h.right h.left

Conclusion ""
