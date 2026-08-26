import Game.Levels.PfWorld.L12_pf

World "PfWorld"
Level 13

Title "Example 13"

Introduction "
# **Level 13**
"

Statement : ∃! (d : Int), ∀ (x : Int), d * x = 0 := by
  exist! 0
  intro x
  simplify
  intro y h
  obtain h' := h 1
  rw[← h']
  simplify

Conclusion ""

NewTactic exist!
