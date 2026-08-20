import Game.Levels.PfWorld
import Game.Levels.PfWorld.PfWorld_eg.pf_eg_docs
import Game.Metadata

World "PfWorld_eg"
Level 1

Title "Example 1"

Introduction "
### **Level 1**
"

Statement (m n : Int) :  (¬ isEven (m * n)) → (¬ isEven m ∧ ¬ isEven n) := by
  contrapose!
  intro h
  by_cases hm : isEven m
  obtain ⟨k,hk⟩ := hm
  use k * n
  rw[hk]
  simplify
  obtain hn := h hm
  obtain ⟨k,hk⟩ := hn
  use m * k
  rw[hk]
  simplify


Conclusion ""
