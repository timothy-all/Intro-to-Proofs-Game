import Game.Levels.TimWorld.L02_Tim

World "TimWorld"
Level 3

Title "Test"

Introduction "
### **🤔 Level 3?**
"

set_option pp.parens true

/--
Tactic intro
-/
TacticDoc intro

Statement (P Q R : Prop) (h1 : P → Q) ( h2 : Q → R) : (P → R) := by
  intro h3
  exact h2 (h1 h3)

Conclusion ""

NewTactic intro
