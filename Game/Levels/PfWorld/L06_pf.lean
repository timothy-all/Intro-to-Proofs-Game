import Game.Levels.PfWorld.L05_pf

World "PfWorld"
Level 6

Title "Example 6"

Introduction "
### **Level 6**
"

Statement : ∀ n : Int, Divides 21 n → ( Divides 7 n ∧ Divides 3 n) := by
  intro n h
  obtain ⟨k,hk⟩ := h
  constructor
  use 3 * k
  rw[← hk]
  simplify
  use 7 * k
  rw[← hk]
  simplify

Conclusion ""

NewTactic constructor
