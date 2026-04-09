import Game.Levels.SetWorld.SetWorld_eg.L06_set

World "SetWorld_eg"
Level 7

Title "name"

Introduction "
### **Level 7**
"

set_option pp.parens true

Statement {u : Type} (A B : Set u) : A \ B = ∅ → A ⊆ B := by
  intro h
  intro x hx
  rw[Set.eq_empty_iff_forall_notMem] at h
  obtain hx' := h x
  rw[Set.mem_diff] at hx'
  rw[Not_and] at hx'
  rw[Not_not] at hx'
  rw[← Imp_iff_not_or] at hx'
  exact hx' hx


Conclusion ""
