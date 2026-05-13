import Game.Levels.PfWorld.L10_pf

World "PfWorld"
Level 11

Title "Example 11"

Introduction "
### **Level 11**
"

Statement : ∃! (d : Int), ∀ (x : Int), d * x = 0 := by
  use! 0
  refine ⟨?_,?_⟩
  intro x
  simplify
  intro y h
  obtain h' := h 1
  rw[← h']
  simplify


Conclusion ""
