import Game.Levels.SetWorld.SetWorld_eg.L02_set

World "SetWorld_eg"
Level 3

Title "Example 3"

Introduction "
# **Level 3**
Here's a venn diagram with $A ∪ (B \\setminus C)$ (or equivalently $(A ∪ B) \\setminus (C \\setminus A)$) shaded.
![A venn diagram of A union the difference of B and C](images/venn_example3a.png)
"

set_option pp.parens true

open Set

/-- The union of $A$ with $B \setminus C$ is equal to the union of $A$ and $B$ less $C \setminus A$.-/
Statement {u : Type} (A B C : Set u) : A ∪ (B \ C) = (A ∪ B) \ (C \ A) := by
  rw[set_eq_iff]
  intro x
  rw[mem_union_iff]
  rw[mem_diff_iff]
  rw[mem_diff_iff]
  rw[mem_union_iff]
  rw[mem_diff_iff]
  rw[Not_and]
  rw[Or_and_left]
  rw[Or_comm (x ∈ A) (x ∉ C)]
  rw[Not_not]


Conclusion ""
