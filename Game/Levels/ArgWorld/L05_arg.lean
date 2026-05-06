import Game.Levels.ArgWorld.L04_arg

World "ArgWorld"
Level 5

Title "Example 5"

Introduction "
### **Level 5**

"

set_option pp.parens true


Statement (P Q R : Prop) (hPQ : P → Q) (hPR : P → R) (hP : P) : (Q ∧ R) := by
  obtain hQ := hPQ hP
  obtain hR := hPR hP
  obtain hQR := And.intro hQ hR
  exact hQR
  -- one shot with : exact And.intro (hPQ hP) (hQR hR)

Conclusion ""
