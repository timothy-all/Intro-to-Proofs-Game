import Game.Levels.PfWorld.L10_pf
import Mathlib.Tactic.Ring

World "PfWorld"
Level 11

Title "Example 11"

Introduction "
### **Level 11**
"

Statement : ∃! (d : Int), ∀ (x : Int), d * x = 0 := by
  unique_use 0
  refine ⟨?_,?_⟩
  intro x
  ring
  intro y h
  obtain h' := h 1
  rw[← h']
  ring


Conclusion ""
