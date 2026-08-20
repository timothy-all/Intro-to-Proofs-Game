import Game.Levels.SetWorld.SetWorld_eg.L05_set

World "SetWorld_eg"
Level 6

Title "name"

Introduction "
### **Level 6**
"

set_option pp.parens true
open Set

Statement Symm_diff_self {u : Type*} {A: Set u} : A Δ A = ∅ := by
  rw[set_eq_iff]
  intro x
  rw[mem_symm_diff_iff]
  rw[mem_union_iff]
  rw[mem_diff_iff]
  rw[And_not_self]
  rw[Or_false]
  rw[mem_empty_iff_false]

Conclusion ""

NewDefinition mem_symm_diff_iff

/- Save this for proof by contradiction example
Statement {u : Type} (A B : Set u) : A ⊆ B ↔ A \ B = ∅ := by

Save this for proof of or
Statement {u : Type} (A B C: Set u) : (A ∪ B) \ (C \ A) ⊆ A ∪ (B \ C) := by
-/
