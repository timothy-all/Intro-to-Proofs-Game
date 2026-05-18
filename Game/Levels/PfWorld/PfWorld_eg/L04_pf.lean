import Game.Levels.PfWorld.PfWorld_eg.L03_pf

World "PfWorld_eg"
Level 4

Title "Example 4"

Introduction "
### **Level 4**
"

Statement (a b c : Int) (ha : isEven a) (hbc : (isOdd b) ∧ (isOdd c)) : Divides 4 (a * (b + c)) := by
  rcases ha with ⟨i,hi⟩
  rcases hbc.left with ⟨j,hj⟩
  rcases hbc.right with ⟨k,hk⟩
  use i*j + i*k + i
  rw[hi,hj,hk]
  ring

Conclusion ""
