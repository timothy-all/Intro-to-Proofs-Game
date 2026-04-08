import Game.Levels.SetWorld

World "SetWorld_eg"
Level 1

Title "name"

Introduction "
### **Level 1**
"

Statement {u : Type} (A B : Set u) : A ∩ B = ∅ → A ⊆ A \ B := by
  rw[Set.eq_empty_iff_forall_notMem] -- pretty wordy
  intro h x hxA
  obtain hxB := h x
  rw[Set.mem_inter_iff] at hxB
  rw[Not_and,← Imp_iff_not_or] at hxB
  exact And.intro hxA (hxB hxA)


Conclusion ""

/- proof strategy eg : proof by contradiction-/
example {u : Type} (A B : Set u) : A ⊆ A \ B → A ∩ B = ∅ := by
  intro h
  by_contra! F
  obtain ⟨x,hx⟩ := F
  exact (h hx.left).right hx.right
