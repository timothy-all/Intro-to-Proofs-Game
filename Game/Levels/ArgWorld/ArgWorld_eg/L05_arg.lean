import Game.Levels.ArgWorld.ArgWorld_eg.L04_arg

World "ArgWorld_eg"
Level 5

Title "Test"

Introduction "
### **🤔 Level 5?**
"

set_option pp.parens true


Statement (P Q R S : Prop) (h1 : (P ∧ Q) → S) (h2 : R → ¬ S) (h3 : P ∧ R) : ¬ Q := by
  obtain hS := h2 h3.right
  rw[contrapositive,Not_and] at h1
  obtain hPQ := h1 hS
  rw[← Imp_iff_not_or] at hPQ
  exact hPQ h3.left

Conclusion ""
