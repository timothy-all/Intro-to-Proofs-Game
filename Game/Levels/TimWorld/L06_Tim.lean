import Game.Levels.TimWorld.L05_Tim

World "TimWorld"
Level 6

Title "Test"

Introduction "
### **🤔 Level 6?**
"

/--
Suppose $P$, $Q$, and $R$ are propositions. If $P → Q → R$ is true, then $(P ∧ Q) → R$ is true.
-/
TheoremDoc curry_right as "curry_right"

Statement curry_right (P Q R : Prop) : (P → Q → R) → ((P ∧ Q) → R) := by
  intro h hPQ
  obtain h1 := h hPQ.left
  exact h1 hPQ.right


Conclusion ""

NewTactic obtain
