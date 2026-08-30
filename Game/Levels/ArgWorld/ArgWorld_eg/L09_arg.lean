import Game.Levels.ArgWorld.ArgWorld_eg.L08_arg

World "ArgWorld_eg"
Level 9

Title "Example 7"

Introduction "
# **Level 9**
One interesting way to try to prove an `∨`-statement is to convert it into a `→`-statement with `Imp_iff_not_or`. That might be helpful here...
"

set_option pp.parens true


Statement (P Q R S : Prop) (h1: S → R) (h2 : ¬ (P ∧ R)) : ¬ P ∨ ¬ S := by
  rw[← Imp_iff_not_or]
  intro hP
  rw[Not_and,← Imp_iff_not_or] at h2
  obtain hR := h2 hP
  rw[Contrapositive] at h1
  exact h1 hR

Conclusion ""
