import Game.Levels.PfWorld.L02_pf
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

World "PfWorld"
Level 3

Title "Example 3"

Introduction "
### **Level 3**
"

Statement (P Q R : Prop) : (¬ R → (P → ¬ Q)) → (P → (Q → R)) := by
  intro h hP hQ
  by_contra F
  obtain hQ' := h F hP
  contradiction



Conclusion ""

NewTactic by_contra contradiction
