import Game.Levels.SetWorld.SetWorld_eg.L06_set

World "SetWorld_eg"
Level 7

Title "name"

Introduction "
### **Level 7**
"

set_option pp.parens true

open Set

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

NewTheorem not_false_iff
