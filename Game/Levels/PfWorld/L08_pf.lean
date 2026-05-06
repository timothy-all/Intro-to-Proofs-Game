import Game.Levels.PfWorld.L07_pf
import Mathlib.Tactic.Ring

World "PfWorld"
Level 8

Title "Example 8"

Introduction "
### **Level 8**
"

Statement (n : Int) : Divides 40 n ↔ (Divides 8 n ∧ Divides 5 n) := by
  constructor
  intro ⟨k,hk⟩
  constructor
  use 5 * k
  rw[← hk]
  ring
  use 8 * k
  rw[← hk]
  ring
  intro ⟨⟨k,hk⟩, ⟨j,hj⟩⟩
  obtain h1 : 15 * n = 120 * k
  rw[← hk]
  ring
  obtain h2 : 16 * n = 80 * j
  rw[← hj]
  ring
  obtain h3 : n = 80 * j - 120 * k
  rw[← h1,← h2]
  ring
  use 2*j - 3*k
  rw[h3]
  ring










Conclusion ""
