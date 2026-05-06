import Game.Levels.SetWorld.SetWorld_eg

/- Proof-strategy : AND-goal -/
example {u : Type} (A B: Set u) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B := by
  apply Set.ext
  intro x
  constructor
  intro hx
  exact h1 hx
  intro hx
  exact h2 hx


/- proof strategy eg : proof by contradiction-/
example {u : Type} (A B : Set u) : A ⊆ A \ B → A ∩ B = ∅ := by
  intro h
  by_contra! F
  obtain ⟨x,hx⟩ := F
  exact (h hx.left).right hx.right


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

example (P Q : Prop) (h1 : P → Q) (h2 : ¬ P → Q) : Q := by
  by_contra F
  rw[Contrapositive] at h2 h1
  rw[Not_not] at h2
  exact (h1 F) (h2 F)

Conclusion ""
