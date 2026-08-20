import Game.Levels.PfWorld.PfWorld_eg.L03_pf

World "PfWorld_eg"
Level 4

Title "Example 4"

Introduction "
### **Level 4**
"

Statement (a b c : Int) (ha : isEven a) (hbc : (isOdd b) ∧ (isOdd c)) : Divides 4 (a * (b + c)) := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hbc.left
  obtain ⟨k,hk⟩ := hbc.right
  use i*j + i*k + i
  rw[hi,hj,hk]
  simplify

Conclusion ""
