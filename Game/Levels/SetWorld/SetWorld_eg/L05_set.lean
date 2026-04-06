import Game.Levels.SetWorld.SetWorld_eg.L04_set

World "SetWorld_eg"
Level 5

Title "name"

Introduction "
### **Level 5**
"

set_option pp.parens true

Statement {u : Type} (A B C : Set u) : C \ A ⊆ B → C ⊆ A ∪ B := by
  intro h x
  rw[Imp_iff_not_or]
  rw[Set.mem_union]
  rw[← Or_assoc]
  rw[← Not_not (x ∈ A)]
  rw[← Not_and]
  rw[← Set.mem_diff]
  rw[← Imp_iff_not_or]
  intro hx
  exact h hx

Conclusion ""
