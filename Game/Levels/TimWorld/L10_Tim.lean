import Game.Levels.TimWorld.L09_Tim

World "TimWorld"
Level 10

Title "Test"

Introduction "
### **🤔 Level 10?**
"


/--
Suppose $P$ and $Q$ are propositions. If $P → Q$ is true, then $¬ P ∨ Q$ is true.
-/
TheoremDoc cond_law_left as "cond_law_left"

Statement (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro nPQ hP
  rcases nPQ with nP | hQ
  contradiction
  exact hQ

Conclusion ""

NewTactic rcases contradiction
