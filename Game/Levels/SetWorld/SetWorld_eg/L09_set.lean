import Game.Levels.SetWorld.SetWorld_eg.L08_set

World "SetWorld_eg"
Level 9

Title "name"

Introduction "
### **Level 9**
"

set_option pp.parens true








Conclusion ""

/- Proof-strategy : Or-as-hypothesis -/
example {u : Type} (F G : Set (Set u)) : ⋂₀ F ∩ ⋂₀ G ⊆ ⋂₀ (F ∪ G) := by
  intro x ⟨hxF,hxG⟩ X hX -- or destructure with obtain
  rw[Set.mem_union] at hX
  cases hX -- or rcases with ...
  exact hxF X h
  exact hxG X h

/- Proof-strategy : And-as-goal -/
example {u : Type} (F G : Set (Set u)) : ⋂₀ (F ∪ G) ⊆ ⋂₀ F ∩ ⋂₀ G  := by
  intro x hx
  refine ⟨?xinF,?xinG⟩
  intro X hXF
  obtain hXFG := Or.intro_left (X ∈ G) hXF
  rw[← Set.mem_union] at hXFG
  exact hx X hXFG
  intro X hXG
  obtain hXFG := Or.intro_right (X ∈ F) hXG
  rw[← Set.mem_union] at hXFG
  exact hx X hXFG


example {u : Type*} {I : Type*} (A B : I → Set u) : ⋂ i, (A i \ B i) ⊆  (⋂ i, A i ) \ (⋃ i, B i) := by
  intro x hx
  constructor
  rw[mem_iinter] at hx ⊢
  intro i
  exact (hx i).left
  simp at hx ⊢
  intro i
  exact (hx i).right
