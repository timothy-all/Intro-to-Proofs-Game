import Game.Levels.TimWorld.L06_Tim

World "TimWorld"
Level 7

Title "Test"

Introduction "
### **🤔 Level 7?**
"

/--
Suppose $P$ and $Q$ are propositions. If $P$ and $Q$ are true, then $P ∧ Q$ is true. The **constructor** for the `∧` connective is `And.intro`. Specifically:
```
And.intro (P Q : Prop) : P → Q → (P ∧ Q)
```
-/
DefinitionDoc And.intro as "And.intro"

/--
Suppose $P$, $Q$, and $R$ are propositions. If $P → Q → R$ is true, then $(P ∧ Q) → R$ is true.
-/
TheoremDoc curry_left as "curry_left"

Statement curry_left (P Q R : Prop) : ((P ∧ Q) → R) → (P → Q → R) := by
  intro hPQ hP hQ
  obtain h := And.intro hP hQ
  exact hPQ h



Conclusion ""

NewDefinition And.intro
