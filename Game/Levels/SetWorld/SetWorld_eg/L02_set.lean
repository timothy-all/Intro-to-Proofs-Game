import Game.Levels.SetWorld.SetWorld_eg.L01_set

World "SetWorld_eg"
Level 2

Title "Example 2"

Introduction "
# **Level 2**
"
set_option pp.parens true

open Set

/-- The set $A$ less $B$ with $C$ removed from the result is equal to $A$ less the union of $B$ and $C$.-/
Statement {u : Type} (A B C : Set u) : (A \ B) \ C = A \ (B ∪ C) := by
  rw[set_eq_iff]
  intro x
  rw[mem_diff_iff,mem_diff_iff,mem_diff_iff]
  rw[mem_union_iff]
  rw[Not_or]
  rw[And_assoc]



Conclusion ""
