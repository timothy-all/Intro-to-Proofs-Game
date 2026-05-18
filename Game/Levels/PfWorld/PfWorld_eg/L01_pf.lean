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
  rcases hm with ⟨k,hk⟩
  use k * n
  rw[hk]
  ring
  obtain hn := h hm
  rcases hn with ⟨k,hk⟩
  use m * k
  rw[hk]
  ring


Conclusion ""
