import Game.Levels.PfWorld.L04_pf

World "PfWorld"
Level 5

Title "Example 5"

Introduction "
### **Level 5**
"

Statement (n : Int) : isOdd n → Divides 4 (n^2-1) := by
  intro h
  obtain ⟨k,hk⟩ := h
  use k^2 + k
  rw[hk]
  simplify

Conclusion ""
