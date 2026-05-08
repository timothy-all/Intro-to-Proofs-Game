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

/- Proof-strategy : And-as-goal !! This is already in set world!! -/
example {u : Type*} {I : Type*} (A B : I → Set u) : ⋂ i, (A i \ B i) ⊆  (⋂ i, A i ) \ (⋃ i, B i) := by
  intro x hx
  constructor
  rw[mem_iinter] at hx ⊢
  intro i
  exact (hx i).left
  simp at hx ⊢
  intro i
  exact (hx i).right

/- Proof-strategy : contradiction -/
example (P Q : Prop) (h1 : P → Q) (h2 : ¬ P → Q) : Q := by
  by_contra F
  rw[Contrapositive] at h2 h1
  rw[Not_not] at h2
  exact (h1 F) (h2 F)

example {u : Type*} (A B C : Set u) : symmDiff A C ⊆ (symmDiff A B) ∪ (symmDiff B C) := by
  intro x hx
  rcases hx with ⟨hxa,hxc'⟩ | ⟨hxc,hxa'⟩
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

example (a b c : Int) (ha : isEven a) (hbc : (isOdd b) ∧ (isOdd c)) : Divides 4 (a * (b + c)) := by
  rcases ha with ⟨i,hi⟩
  rcases hbc.left with ⟨j,hj⟩
  rcases hbc.right with ⟨k,hk⟩
  use i*j + i*k + i
  rw[hi,hj,hk]
  ring

example (m n : Int) :  (¬ isEven (m * n)) → (¬ isEven m ∧ ¬ isEven n) := by
  contrapose!
  intro h
  by_cases hm : isEven m
  rcases hm with ⟨k,hk⟩
  use k * n
  rw[hk]
  ring
  obtain hn := h hm
  rcases hn with ⟨k,hk⟩
  use m * k
  rw[hk]
  ring

example (n : Int) : ( Divides 5 n ∧ Divides 13 n) ↔ Divides 65 n := by
  constructor
  intro h
  rcases h.left with ⟨j,hj⟩
  rcases h.right with ⟨k,hk⟩
  obtain hj' : 26 * 5 * j = 26 * n
  rw[← hj]
  ring
  obtain hk' : 25 * 13 * k = 25 * n
  rw[← hk]
  ring
  obtain want : n = 26 * 5 * j - 25 * 13 * k
  rw[hj',hk']
  ring
  use 2 * j - 5 * k
  rw[want]
  ring
  intro ⟨k,hk⟩
  constructor
  use 13 *k
  rw[← hk]
  ring
  use 5 * k
  rw[← hk]
  ring

example {u : Type*} (A B C : Set u) : C ⊆ symmDiff A B ↔ (C ⊆ A ∪ B ∧ (A ∩ B ∩ C = ∅ )) := by
  constructor
  intro hC
  constructor
  intro c hc
  obtain hc' := hC hc
  rcases hc' with ⟨hcA,hcB'⟩ | ⟨hcB,hcA'⟩
  left
  exact hcA
  right
  exact hcB
  rw[Set.eq_empty_iff_forall_notMem]
  intro x
  by_contra! F
  obtain F' := hC F.right
  rcases F' with ⟨hxA,hxB'⟩ | ⟨hxB,hxA'⟩
  exact hxB' F.left.right
  exact hxA' F.left.left
  intro ⟨hC,h⟩
  intro c hc
  obtain hc' := hC hc
  rcases hc' with hcA | hcB
  left
  refine ⟨hcA,?_⟩
  by_contra!
  obtain that : c ∈ A ∩ B ∩ C := And.intro (And.intro hcA this) hc
  rw[h] at that
  contradiction
  right
  refine ⟨hcB,?_⟩
  by_contra!
  obtain that : c ∈ A ∩ B ∩ C := And.intro (And.intro this hcB) hc
  rw[h] at that
  contradiction

example {u : Type*} (U : Set u) : ∃! I ⊆ U, ∀ A ⊆ U, symmDiff A I = A := by
  use ∅
  constructor
  constructor
  intro x hx
  contradiction
  -- apply Set.empty_subset -- this works instead of intro/contradiction
  intro A hA
  rw[Set.ext_iff]
  intro x
  constructor
  intro hx
  rcases hx with ⟨hxA,F'⟩ | ⟨F,hxA'⟩
  exact hxA
  contradiction
  intro hxA
  left
  constructor
  exact hxA
  by_contra!
  contradiction
  intro I hI
  by_contra!
  rw[Set.nonempty_def] at this
  rcases this with ⟨i,hi⟩
  obtain F := hI.right I hI.left
  rw[← F] at hi
  rw[Set.symmDiff_self] at hi
  contradiction

example {u : Type*} (U : Set u) : ∀ A ⊆ U, ∃! B ⊆ U, symmDiff A B = ∅ := by
  intro A hA
  use A
  constructor
  constructor
  exact hA
  exact Set.symmDiff_self A
  intro B hB
  rw[Set.ext_iff]
  intro x
  constructor
  intro hxB
  by_contra!
  obtain that : x ∈ symmDiff A B
  right
  exact And.intro hxB this
  rw[hB.right] at that
  contradiction
  intro hxA
  by_contra!
  obtain that : x ∈ symmDiff A B
  left
  exact And.intro hxA this
  rw[hB.right] at that
  contradiction

example {u : Type*} (A B C : Set u) : (A \ B) \ C ⊆ A \ (B \ C) := by
  intro x hx
  constructor
  exact hx.left.left
  by_contra!
  exact hx.left.right this.left --this is dumb

example {u : Type*} (A B C : Set u) : A ∩ C = ∅ → A \ (B \ C) ⊆ (A \ B) \ C := by
  sorry

example {u : Type*} (F G H : Set (Set u)) : (∀ A ∈ F, ∀ B ∈ G, A ∪ B ∈ H) → ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := by
  sorry

/- misc -/

lemma mem_bunion (u : Type*) (F : Set (Set u)) (x : u) (s : Set u → Set u) : x ∈ ⋃ X ∈ F, s X ↔ ∃ X ∈ F, x ∈ s X := by
  simp

example (u : Type*) (F : Set (Set u)) (A : u → Set u) ( I : Set u): I = ⋃₀ F → (⋃ i ∈ I, A i = ⋃ X ∈ F, (⋃ j ∈ X, A j)) := by
  intro h
  rw[Set.ext_iff]
  intro x
  constructor
  intro hx
  rw[mem_iunion] at hx
  rcases hx with ⟨i,⟨A',⟨⟨hi,hA'⟩,hx'⟩⟩⟩ -- this is dumb
  dsimp at hA'
  rw[h] at hi
  rw[mem_funion] at hi -- haha, funions
  rcases hi with ⟨X,hX⟩
  apply Set.mem_biUnion hX.left
  apply Set.mem_biUnion hX.right
  rw[hA']
  exact hx'
  intro hx
  rw[mem_bunion] at hx
  rcases hx with ⟨X,⟨hX,hX'⟩⟩
  rw[mem_iunion] at hX'
  rcases hX' with ⟨i,⟨A',⟨⟨hi,hA'⟩,hx'⟩⟩⟩ -- this is dumb
  dsimp at hA'
  rw[← hA'] at hx'
  rw[mem_iunion]
  use i
  use A i
  constructor
  simp -- sigh
  rw[h]
  use X
  exact hx'

Conclusion ""
