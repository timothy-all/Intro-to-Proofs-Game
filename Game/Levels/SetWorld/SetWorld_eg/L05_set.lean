import Game.Levels.SetWorld.SetWorld_eg.L04_set

World "SetWorld_eg"
Level 5

Title "name"

Introduction "
### **Level 5**
"

set_option pp.parens true

open Set

Statement {u : Type} (A B C : Set u) : C \ A ⊆ B → C ⊆ A ∪ B := by
  intro h x
  rw[Imp_iff_not_or]
  rw[mem_union_iff]
  rw[← Or_assoc]
  rw[← Not_not (x ∈ A)]
  rw[← Not_and]
  rw[← mem_diff_iff]
  rw[← Imp_iff_not_or]
  intro hx
  exact h hx

Conclusion ""
