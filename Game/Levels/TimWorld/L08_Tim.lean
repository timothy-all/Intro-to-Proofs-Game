import Game.Levels.TimWorld.L07_Tim

World "TimWorld"
Level 8

Title "Test"

Introduction "
### **🤔 Level 8?**
"


/--
Suppose $P$, $Q$, and $R$ are propositions. If $P → Q → R$ is true, then $(P ∧ Q) → R$ is true.
-/
TheoremDoc curry_left as "curry_left"

Statement (P Q R : Prop) : ((P ∧ Q) → R) → (P → Q → R) := by
  intro hPQ hP hQ
  obtain h := And.intro hP hQ
  exact hPQ h



Conclusion ""
