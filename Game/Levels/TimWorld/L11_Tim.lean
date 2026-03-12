import Game.Levels.TimWorld.L10_Tim

World "TimWorld"
Level 11

Title "Test"

Introduction "
### **🤔 Level 11?**
"


/--
Suppose $P$ and $Q$ are propositions. If $P → Q$ is true, then $¬ P ∨ Q$ is true.
-/
TheoremDoc DeMorgan_right as "DeMorgan_right"

Statement DeMorgan_right (P Q : Prop) : ¬ (P ∧ Q) →  (¬ P ∨ ¬ Q):= by
  intro h
  by_cases hP : P
  by_cases hQ : Q
  obtain hPQ := And.intro hP hQ
  contradiction
  right
  exact hQ
  left
  exact hP


Conclusion ""

NewTactic obtain
