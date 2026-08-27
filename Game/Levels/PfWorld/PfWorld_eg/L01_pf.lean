import Game.Levels.PfWorld
import Game.Levels.PfWorld.PfWorld_eg.pf_eg_docs
import Game.Metadata

World "PfWorld_eg"
Level 1

Title "Example 1"

Introduction "
# **Level 1**
"

Statement (m n : Int) :  (¬ isEven (m * n)) → (¬ isEven m ∧ ¬ isEven n) := by
  contrapose
  rw[Not_and,Not_not,Not_not,Not_not]
  intro h
  obtain ⟨k,hk⟩ | ⟨j,hj⟩ := h
  exist k * n
  rw[hk]
  simplify
  exist j * m
  rw[hj]
  simplify


Conclusion ""
