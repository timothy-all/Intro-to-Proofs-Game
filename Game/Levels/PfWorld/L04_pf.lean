import Game.Levels.PfWorld.L03_pf

World "PfWorld"
Level 4

Title "Example 4"

Introduction "
### **Level 4**
"

Statement (x y : Int) : ¬ isOdd (x * y) → ¬ (isOdd x ∧ isOdd y) := by
  contrapose!
  intro h
  rw[isOdd]
  obtain ⟨⟨c,hc⟩,⟨d,hd⟩⟩ := h
  use 2* c * d + c + d
  rw[hc,hd]
  simplify

Conclusion ""

NewTactic contrapose!
NewDefinition isOdd
