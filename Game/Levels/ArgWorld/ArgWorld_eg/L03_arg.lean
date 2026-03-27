import Game.Levels.ArgWorld.ArgWorld_eg.L02_arg

World "ArgWorld"
Level 3

Title "Test"

Introduction "
### **🤔 Level 3?**
"

set_option pp.parens true

/--
obtain doc
-/
TacticDoc obtain

Statement (P Q R S T: Prop) (h1 : P → (Q → R)) (h2 : P ∨ S) (h3 : T → Q) (h4 : ¬ S) : ¬ R → ¬ T := by
  rw[← Not_not S,Or_comm,← Imp_iff_not_or] at h2
  obtain hP := h2 h4
  obtain hQR := h1 hP
  rw[contrapositive] at hQR h3
  intro hR
  exact h3 (hQR hR)

Conclusion ""

NewTactic obtain
