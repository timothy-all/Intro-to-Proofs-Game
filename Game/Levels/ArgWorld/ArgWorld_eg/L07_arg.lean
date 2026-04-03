import Game.Levels.ArgWorld.ArgWorld_eg.L06_arg

World "ArgWorld_eg"
Level 7

Title "Test"

Introduction "
### **🤔 Level 7?**
"

set_option pp.parens true


Statement (P Q R  : Prop) (h1 : P ∨ (R ∧ Q)) (h2 : P → Q) : ¬ R → Q := by
  intro hR
  rw[Or_and_left] at h1
  obtain h := And.intro h1.left hR
  rw[And_comm,And_or_left,And_comm (¬ R) R,And_not_self,Or_false] at h
  exact h2 h.right

Conclusion ""
