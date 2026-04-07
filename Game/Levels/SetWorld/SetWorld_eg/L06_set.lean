import Game.Levels.SetWorld.SetWorld_eg.L05_set

World "SetWorld_eg"
Level 6

Title "name"

Introduction "
### **Level 6**
"

set_option pp.parens true

Statement {u : Type} (A : Set u) (F : Set (Set u)) (h : A ∈ F) : ⋂₀ F ⊆ A := by
  intro a ha
  /- ⋂₀ F is sugar for InfSet F; the membership proposition x ∈ ⋂₀ F unpacks to ∀ (t : Set (Set u)), t ∈ F → x ∈ t. -/
  exact ha A h


Conclusion ""
