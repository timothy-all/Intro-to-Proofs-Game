import Game.Levels.PfWorld.L01_pf
import Mathlib.Tactic.Ring

World "PfWorld"
Level 2

Title "Example 2"

Introduction "
### **Level 2**
"


Statement (u v : Int) (hu : isEven u) (hv: isEven v) : isEven (u + v) := by
  rw[isEven] at hu hv
  rcases hu with ⟨k,hk⟩
  rcases hv with ⟨l,hl⟩
  use k+l
  rw[hk,hl]
  ring




Conclusion ""
