import Game.Levels.PfWorld.PfWorld_eg.L08_pf

World "PfWorld_eg"
Level 9

Title "Example 9"

Introduction "
### **Level 9**
"

Statement {u : Type*} (A B C : Set u) : A Δ C ⊆ (A Δ B) ∪ (B Δ C) := by
  intro x hx
  obtain ⟨hxa,hxc'⟩ | ⟨hxc,hxa'⟩ := hx
  by_cases hxb : x ∈ B
  right
  left
  exact And.intro hxb hxc'
  left
  left
  exact And.intro hxa hxb
  by_cases hxb : x ∈ B
  left
  right
  exact And.intro hxb hxa'
  right
  right
  exact And.intro hxc hxb

Conclusion ""
