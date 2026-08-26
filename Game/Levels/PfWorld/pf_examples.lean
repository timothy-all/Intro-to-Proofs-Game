import Game.Levels.PfWorld


/- Proof-strategy : AND-goal -/
example {u : Type} (A B: Set u) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B := by
  rw[Set.ext_iff]
  intro x
  constructor
  intro hx
  exact h1 hx
  intro hx
  exact h2 hx



--same example different way

/- indirect contraposition -/
example {u : Type*} (A B C : Set u) : A ∩ C = ∅ → A \ (B \ C) ⊆ (A \ B) \ C := by
  contrapose!
  intro h
  rw[Set.subset_def] at h
  push_neg at h
  rcases h with ⟨x,hx⟩
  use x
  obtain hxA : x ∈ A := hx.left.left
  obtain hxC : x ∈ C
  rw[Set.mem_diff,Set.mem_diff,Set.mem_diff,Set.mem_diff] at hx
  rw[Not_and,Not_and,Not_and] at hx
  rw[Not_not,Not_not] at hx
  by_cases hxB : x ∈ B
  rcases hx.left.right with hxB' | hxC
  contradiction
  exact hxC
  rcases hx.right with ⟨hxA' | hxB⟩ | hxC
  contradiction
  contradiction
  exact hxC
  exact And.intro hxA hxC


/- misc -/

lemma mem_bunion (u : Type*) (F : Set (Set u)) (x : u) (s : Set u → Set u) : x ∈ ⋃ X ∈ F, s X ↔ ∃ X ∈ F, x ∈ s X := by
  simp

example (u : Type*) (F : Set (Set u)) (A : u → Set u) ( I : Set u): I = ⋃₀ F → (⋃ i ∈ I, A i = ⋃ X ∈ F, (⋃ j ∈ X, A j)) := by
  intro h
  rw[Set.ext_iff]
  intro x
  constructor
  intro hx
  rw[mem_iunion_iff] at hx
  rcases hx with ⟨i,⟨A',⟨⟨hi,hA'⟩,hx'⟩⟩⟩ -- this is dumb
  dsimp at hA'
  rw[h] at hi
  rw[mem_funion_iff] at hi -- haha, funions
  rcases hi with ⟨X,hX⟩
  apply Set.mem_biUnion hX.left
  apply Set.mem_biUnion hX.right
  rw[hA']
  exact hx'
  intro hx
  rw[mem_bunion] at hx
  rcases hx with ⟨X,⟨hX,hX'⟩⟩
  rw[mem_iunion_iff] at hX'
  rcases hX' with ⟨i,⟨A',⟨⟨hi,hA'⟩,hx'⟩⟩⟩ -- this is dumb
  dsimp at hA'
  rw[← hA'] at hx'
  rw[mem_iunion_iff]
  use i
  use A i
  constructor
  simp -- sigh
  rw[h]
  use X
  exact hx'

Conclusion ""
