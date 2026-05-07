import Game.Levels.PfWorld.L08_pf
import Mathlib.Tactic.Ring

World "PfWorld"
Level 9

Title "Example 9"

Introduction "
### **Level 9**
"

Statement (u : Type*) (A B : Set u) : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B → (A ⊆ B ∨ B ⊆ A) := by
  contrapose!
  intro ⟨h1,h2⟩
  rw[Set.subset_def] at h1
  push_neg at h1
  rw[Set.subset_def] at h2
  push_neg at h2
  rcases h1 with ⟨a,ha⟩
  rcases h2 with ⟨b,hb⟩
  unfold Ne
  rw[Set.ext_iff]
  push_neg
  use {a,b}
  constructor
  constructor
  intro x hx
  cases hx
  rw[h]
  left
  exact ha.left
  cases h
  right
  exact hb.left
  rw[Set.mem_union]
  push_neg
  constructor
  rw[Set.mem_powerset_iff]
  rw[subset_def]
  push_neg
  use b
  constructor
  right
  /-
  It seems x ∈ {a,b} is shorthand for x = a ∨ x ∈ {b}. I think this is because Set.insert is the underlying mechanism by which Lean interprets something like {a,b,c}.
  -/
  rfl
  /-
  Similarly, x ∈ {y} is shorthand for x = y. This, I think, is why rfl clears the goal.
  -/
  exact hb.right
  rw[Set.mem_powerset_iff]
  rw[subset_def]
  push_neg
  use a
  constructor
  left
  rfl
  exact ha.right

Conclusion ""
