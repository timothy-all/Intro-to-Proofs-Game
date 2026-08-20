import Game.Levels.PfWorld.L01_pf
--import Mathlib.Tactic.Ring

World "PfWorld"
Level 2

Title "Example 2"

Introduction "
### **Level 2**
"


Statement (u v : Int) (hu : isEven u) (hv: isEven v) : isEven (u + v) := by
  rw[isEven] at hu hv
  obtain ⟨k,hk⟩ := hu
  obtain ⟨l,hl⟩ := hv
  use k+l
  rw[hk,hl]
  simplify

Conclusion ""

NewDefinition isEven
NewTactic simplify
