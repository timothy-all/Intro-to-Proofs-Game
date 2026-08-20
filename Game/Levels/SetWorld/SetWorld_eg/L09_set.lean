import Game.Levels.SetWorld.SetWorld_eg.L08_set

World "SetWorld_eg"
Level 9

Title "name"

Introduction "
### **Level 9**
"

set_option pp.parens true

Statement Set.symmDiff_self {u : Type*} (A : Set u) : symmDiff A A = ∅ := by
  rw[set_eq_iff]
  intro x
  constructor
  intro hx
  rcases hx with ⟨hxA,hxA'⟩ | ⟨hxA,hxA'⟩
  contradiction
  contradiction
  intro hx
  contradiction

Conclusion ""
