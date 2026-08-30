import Game.Levels.SetWorld
import Game.Levels.SetWorld.SetWorld_eg.set_eg_docs
import Game.Levels.SetWorld.Metadata_setworld
import Game.Levels.QuantifierWorld.QuantifierWorld_eg

World "SetWorld_eg"
Level 1

Title "Example 1"

Introduction "
# **Level 1**
"
open Set

set_option pp.parens true

/-- The set $A \setminus B$ intersected with $A$ is equal to $A \setminus B$.-/
Statement {u : Type*} (A B C : Set u) : (A \ B) ∩ A = A \ B := by
  rw[set_eq_iff]
  intro x
  rw[mem_inter_iff]
  rw[mem_diff_iff]
  rw[And_comm]
  rw[← And_assoc]
  rw[And_self]

Conclusion ""


--Statement {u : Type} (A B : Set u) : A ∩ B = ∅ → A ⊆ A \ B := by
