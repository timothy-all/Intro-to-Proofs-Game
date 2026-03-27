import Game.Levels.TimWorld.L07_Tim

World "TimWorld"
Level 8

Title "Test"

Introduction "
### **🤔 Level 8?**
"

/--
obtain doc
-/
TacticDoc obtain

Statement (P Q R S T: Prop) (h1 : P → (Q → R)) (h2 : P ∨ S) (h3 : T → Q) (h4 : ¬ S) : ¬ R → ¬ T := by
  rw[← Not_not S,Or_comm,Or_imp] at h2
  obtain hP := h2 h4
  obtain hQR := h1 hP
  rw[Contrapos] at hQR h3
  intro hR
  exact h3 (hQR hR)

Conclusion ""

NewTactic obtain
