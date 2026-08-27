import Game.Levels.SetWorld.SetWorld_eg.L05_set

World "SetWorld_eg"
Level 6

Title "name"

Introduction "
### **Level 6**
"

set_option pp.parens true
open Set

Statement {u : Type*} {A B : Set u} : A \ B = ∅ → A Δ B = B \ A := by
  intro h
  rw[set_eq_iff]
  intro x
  rw[mem_symm_diff_iff]
  rw[mem_union_iff]
  rw[h]
  rw[mem_empty_iff_false]
  rw[Or_comm, Or_false]

Conclusion ""


/- Save this for proof by contradiction example
Statement {u : Type} (A B : Set u) : A ⊆ B ↔ A \ B = ∅ := by

Save this for proof of or
Statement {u : Type} (A B C: Set u) : (A ∪ B) \ (C \ A) ⊆ A ∪ (B \ C) := by
-/
