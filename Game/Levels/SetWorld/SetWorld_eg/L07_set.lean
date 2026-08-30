import Game.Levels.SetWorld.SetWorld_eg.L06_set

World "SetWorld_eg"
Level 7

Title "Example 7"

Introduction "
# **Level 7**
Possibly depending on how you go about things, you might find the following freshly unlocked theorem helpful here:
```
not_false_iff : ¬ False ↔ True
```
"

set_option pp.parens true

open Set

/-- The symmetric difference between $A$ and the empty set is equal to $A$.-/
Statement {u : Type} (A : Set u) : A Δ ∅ = A := by
  rw[set_eq_iff]
  intro x
  rw[mem_symm_diff_iff]
  rw[mem_union_iff]
  rw[mem_diff_iff,mem_diff_iff]
  rw[mem_empty_iff_false]
  rw[not_false_iff] -- dumb
  rw[And_true]
  rw[And_comm]
  rw[And_false]
  rw[Or_false]

Conclusion ""

/--
The negation of False is True.
-/
TheoremDoc not_false_iff as "EQU: not_false_iff"

NewTheorem not_false_iff
