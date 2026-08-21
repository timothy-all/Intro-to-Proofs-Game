import Game.Levels.ArgWorld.ArgWorld_eg.L07_arg

World "ArgWorld_eg"
Level 8

Title "Example 6"

Introduction "
# **Level 8**
"

set_option pp.parens true


Statement (P Q R S : Prop) (h1 : (P ∧ Q) → S) (h2 : R → ¬ S) (h3 : P ∧ R) : ¬ Q := by
  rw[Contrapositive,Not_and] at h1
  obtain hPQ := h1 (h2 h3.right)
  rw[← Imp_iff_not_or] at hPQ
  exact hPQ h3.left

Conclusion ""
