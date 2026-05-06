import Game.Levels.PfWorld
import Game.Levels.PfWorld.PfWorld_eg.pf_eg_docs

World "PfWorld_eg"
Level 1

Title "Example 1"

Introduction "
### **Level 1**
"

Statement (u : Type*) (A B C D : Set u) (h : A ∩ B ⊆ C \ D) (x : u) : x ∈ A → (x ∈ D → x ∉ B) := by
  intro hxA
  rw[Contrapositive]
  push_neg
  intro hxB
  obtain want := h (And.intro hxA hxB)
  exact want.right


Conclusion ""
