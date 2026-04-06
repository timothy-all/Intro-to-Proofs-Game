import Game.Levels.SetWorld.SetWorld_eg.L03_set

World "SetWorld_eg"
Level 4

Title "name"

Introduction "
### **Level 4**
"

set_option pp.parens true

Statement {u : Type} (A B C : Set u) : C ⊆ A ∪ B → C \ A ⊆ B := by
  intro h x hx
  rw[Set.mem_diff] at hx
  obtain hC := h hx.left -- the arg of set-containment is implicit here
  rw[Set.mem_union] at hC
  rw[← Not_not (x ∈ A)] at hC
  rw[← Imp_iff_not_or] at hC
  exact hC hx.right

Conclusion ""
