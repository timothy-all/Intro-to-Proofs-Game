import Game.Levels.SetWorld.SetWorld_eg.L05_set

World "SetWorld_eg"
Level 6

Title "name"

Introduction "
### **Level 6**
"

set_option pp.parens true

Statement {u : Type} (A B : Set u) : A ⊆ B → A \ B = ∅ := by
  intro h
  rw[Set.eq_empty_iff_forall_notMem]
  intro
  rw[Set.mem_diff]
  rw[Not_and]
  rw[← Imp_iff_not_or]
  rw[Not_not]
  intro hx
  exact h hx


Conclusion ""
