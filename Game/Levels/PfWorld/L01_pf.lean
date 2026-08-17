import Game.Levels.SetWorld
import Game.Levels.SetWorld.SetWorld_eg
import Game.Levels.PfWorld.Metadata_pfworld
import Game.Levels.PfWorld.pf_docs

World "PfWorld"
Level 1

Title "Example 1"

Introduction "
### **Level 1**
"

Statement (u : Type*) (A B C D : Set u) (h : A ∩ B ⊆ C \ D) (x : u) : x ∈ A → (x ∈ D → x ∉ B) := by
  intro hxA
  contrapose
  rw[Not_not]
  intro hxB
  obtain want := h (And.intro hxA hxB)
  exact want.right


Conclusion ""
