import Game.Levels.PfWorld.L04_pf
import Mathlib.Tactic.Ring

World "PfWorld"
Level 5

Title "Example 5"

Introduction "
### **Level 5**
"

Statement (n : Int) : isOdd n → Divides 4 (n^2-1) := by
  intro h
  rcases h with ⟨k,hk⟩
  use k^2 + k
  rw[hk]
  ring



Conclusion ""
