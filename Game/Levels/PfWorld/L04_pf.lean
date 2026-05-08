import Game.Levels.PfWorld.L03_pf
import Mathlib.Tactic.Ring

World "PfWorld"
Level 4

Title "Example 4"

Introduction "
### **Level 4**
"

Statement (x y : Rat) : (x^2*y = 2*x + y) → (y ≠ 0 → x ≠ 0) := by
  intro h
  contrapose!
  intro hx
  rw[hx] at h
  simp at h
  rw[h]

Conclusion ""

NewTactic contrapose contrapose!
