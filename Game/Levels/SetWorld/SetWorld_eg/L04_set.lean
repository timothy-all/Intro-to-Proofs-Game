import Game.Levels.SetWorld.SetWorld_eg.L03_set

World "SetWorld_eg"
Level 4

Title "Example 4"

Introduction "
# **Level 4**
"

set_option pp.parens true

open Set

Statement {u : Type} (A B C : Set u) : C ⊆ A ∪ B → C \ A ⊆ B := by
  intro h x hx
  rw[mem_diff_iff] at hx
  obtain hC := h hx.left -- the arg of set-containment is implicit here
  rw[mem_union_iff] at hC
  rw[← Not_not (x ∈ A)] at hC
  rw[← Imp_iff_not_or] at hC
  exact hC hx.right

Conclusion ""
