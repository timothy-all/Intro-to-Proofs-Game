import Game.Levels.RelationWorld.Metadata_RelationWorld
import Game.Levels.RelationWorld

World "RelationWorldExamples"
Level 1

Title "Cartesian product Example 1"

Introduction "Double inclusion exercise involving Cartesian products.

Note: It is possible to prove this just using rewrites, but you can also use this to get double inclusion practice. 👉 Start with `apply Double_inclusion` to set up your double inclusion proof."

open Set

/-- If $A, B, C$ are sets, then $A × (B \setminus C) = (A × B) \setminus (A × C).$ -/
Statement (u v: Type) (A: Set u) (B C: Set v) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  apply Double_inclusion
  --rw[subset_def]
  intro x
  intro h
  rw [mem_diff_iff,
    mem_prod_iff, -- mem_prod_iff def
    mem_prod_iff,
    Not_and,
    And_comm (x.1 ∈ A),
    And_assoc,
    And_or_left,
    And_not_self,
    Or_comm,
    Or_false,
    ← And_assoc,
    And_comm (x.2 ∈ B),
    And_assoc,
    ← mem_diff_iff,
    ← mem_prod_iff]
  exact h
  intro x
  intro h
  rw [mem_diff_iff,
    mem_prod_iff,
    mem_prod_iff,
    Not_and,
    And_comm (x.1 ∈ A),
    And_assoc,
    And_or_left,
    And_not_self,
    Or_comm,
    Or_false,
    ← And_assoc,
    And_comm (x.2 ∈ B),
    And_assoc,
    ← mem_diff_iff,
    ← mem_prod_iff] at h
  exact h


Conclusion "This one's kind of tough! Formal mathematics is difficult, but all of the steps even go on under-the-hood in an English proof!"
