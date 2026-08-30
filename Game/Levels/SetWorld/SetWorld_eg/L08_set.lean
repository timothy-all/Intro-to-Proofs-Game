import Game.Levels.SetWorld.SetWorld_eg.L07_set

World "SetWorld_eg"
Level 8

Title "Example 8"

Introduction "
# **Level 8**
This one should give us some practice with intersection and unions of indexed families. 🔓 We've unlocked the definition `mem_iunion_iff`. Check it out in the **Definitions** tab.
"

--set_option pp.parens true

open Set

/-- Suppose two families of sets are indexed over $i ∈ I$, say $A_i$ and $B_i$. The intersection of the $A_i \setminus B_i$ is equal to the intersection of all the $A_i$ less the union of all the $B_i$.
 -/
Statement {u : Type*} {I : Type*} (A B : I → Set u) : ⋂ i, (A i \ B i) = (⋂ i, A i ) \ (⋃ i, B i) := by
  rw[set_eq_iff]
  intro x
  rw[mem_iinter_iff]
  rw[mem_diff_iff]
  rw[mem_iinter_iff]
  rw[mem_iunion_iff]
  rw[Not_exists]
  exact Forall_and  --hmm

Conclusion ""

NewDefinition mem_iunion_iff
