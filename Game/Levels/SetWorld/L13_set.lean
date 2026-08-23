import Game.Levels.SetWorld.L12_set

World "SetWorld"
Level 13

Title "The Power Set"

Introduction "
# **Level 13**
Given a set `A : Set u`, the **power set** of `A`, denoted `𝒫 A` is defined as follows:
```
𝒫 A := {s : Set u | s ⊆ A}
```
So the membership proposition `B ∈ 𝒫 A` means the same thing as `B ⊆ A`.
"
open Set


Statement {u : Type} (A B: Set u) (h : A ⊆ B) : 𝒫 A ⊆ 𝒫 B := by
  intro C hC
  rw[mem_powerset_iff] at hC ⊢
  exact Subseteq_trans hC h


Conclusion ""

NewDefinition Set.mem_powerset_iff
