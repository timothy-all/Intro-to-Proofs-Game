import Game.Levels.PfWorld.PfWorld_eg.L01_pf


World "PfWorld_eg"
Level 2

Title "Example 2"

Introduction "
### **Level 2**
"


Statement {u : Type} (A B : Set u) : A ⊆ A \ B → A ∩ B = ∅ := by
  intro h
  by_contra! F
  obtain ⟨x,hx⟩ := F
  exact (h hx.left).right hx.right




Conclusion ""
