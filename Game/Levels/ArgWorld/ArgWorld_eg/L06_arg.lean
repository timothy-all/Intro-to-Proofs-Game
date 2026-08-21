import Game.Levels.ArgWorld.ArgWorld_eg.L05_arg

World "ArgWorld_eg"
Level 6

Title "Example 4"

Introduction "
# **Level 6**
Here's an abstract example.
"

set_option pp.parens true


Statement (P Q R S T: Prop) (h1 : P → (Q → R)) (h2 : P ∨ S) (h3 : T → Q) (h4 : ¬ S) : ¬ R → ¬ T := by
  rw[← Not_not S,Or_comm,← Imp_iff_not_or] at h2
  obtain hP := h2 h4
  obtain hQR := h1 hP
  rw[Contrapositive] at hQR h3
  intro hR
  exact h3 (hQR hR)

Conclusion "😭 To validate this argument with a truth-table would require 32 rows."
