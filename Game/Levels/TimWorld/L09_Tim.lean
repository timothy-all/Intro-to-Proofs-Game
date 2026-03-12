import Game.Levels.TimWorld.L08_Tim

World "TimWorld"
Level 9

Title "Test"

Introduction "
### **🤔 Level 9?**
"


/--
Suppose $P$ and $Q$ are propositions. If $P → Q$ is true, then $¬ P ∨ Q$ is true.
-/
TheoremDoc cond_law_right as "cond_law_right"

Statement (P Q : Prop) : (P → Q) → (¬ P ∨ Q) := by
  intro h
  by_cases hP : P
  right
  exact h hP
  left
  exact hP

Conclusion ""

NewTactic by_cases
