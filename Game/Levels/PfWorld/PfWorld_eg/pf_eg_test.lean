import Game.Levels.PfWorld
import Game.Levels.PfWorld.PfWorld_eg.pf_eg_docs
import Game.Metadata

/-companion to odd version, by_cases-/
example (m n : Int) :  (¬ isEven (m * n)) → (¬ isEven m ∧ ¬ isEven n) := by
  contrapose!
  intro h
  by_cases hm : isEven m
  obtain ⟨k,hk⟩ := hm
  exist k * n
  rw[hk]
  simplify
  obtain hn := h hm
  obtain ⟨k,hk⟩ := hn
  exist m * k
  rw[hk]
  simplify

/- proof by contradiction-/
example {u : Type*} (A B : Set u) : A ⊆ A \ B → A ∩ B = ∅ := by
  intro h
  by_contra! F
  obtain ⟨x,hx⟩ := F
  exact (h hx.left).right hx.right

/- another proof by contradiction-/
example (P Q : Prop) (h1 : P → Q) (h2 : ¬ P → Q) : Q := by
  by_contra F
  rw[Contrapositive] at h2 h1
  rw[Not_not] at h2
  exact (h1 F) (h2 F)

/- direct proof, unravel the defs-/
example (a b c : Int) (ha : isEven a) (hbc : (isOdd b) ∧ (isOdd c)) : Divides 4 (a * (b + c)) := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hbc.left
  obtain ⟨k,hk⟩ := hbc.right
  exist i*j + i*k + i
  rw[hi,hj,hk]
  simplify

/- direct proof of disjunction/conjunction mix -/
example {u : Type*} (F G : Set (Set u)) : ⋂₀ (F ∪ G) ⊆ ⋂₀ F ∩ ⋂₀ G  := by
  intro x hx
  refine ⟨?xinF,?xinG⟩
  intro X hXF
  apply hx X
  left
  exact hXF
  intro X hXG
  apply hx X
  right
  exact hXG

/- proof of conjunction/disjunction mix -/
example {u : Type*} (A B C : Set u) : (A \ B) \ C ⊆ A \ (B \ C) := by
  intro x hx
  constructor
  exact hx.left.left
  rw[mem_diff_iff]
  rw[Not_and]
  left
  obtain ⟨ ⟨hxA, hxB'⟩,hxC'⟩ := hx
  exact hxB'

/- companion to iff proof in tutorial world-/
example (n : Int) : ( Divides 5 n ∧ Divides 13 n) ↔ Divides 65 n := by
  constructor
  intro h
  obtain ⟨j,hj⟩ := h.left
  obtain ⟨k,hk⟩ := h.right
  obtain hj' : 26 * 5 * j = 26 * n
  rw[← hj]
  simplify
  obtain hk' : 25 * 13 * k = 25 * n
  rw[← hk]
  simplify
  obtain want : n = 26 * 5 * j - 25 * 13 * k
  rw[hj',hk']
  simplify
  exist 2 * j - 5 * k
  rw[want]
  simplify
  intro ⟨k,hk⟩
  constructor
  exist 13 *k
  rw[← hk]
  simplify
  exist 5 * k
  rw[← hk]
  simplify

/- proof using disjunctive hypothesis -/
example {u : Type} (F G : Set (Set u)) : ⋂₀ F ∩ ⋂₀ G ⊆ ⋂₀ (F ∪ G) := by
  intro x ⟨hxF,hxG⟩ X hX -- or destructure with obtain
  rw[mem_union_iff] at hX
  obtain xF | xG := hX -- or rcases with ...
  exact hxF X xF
  exact hxG X xG

/- proof using by_cases and disjunctive hypothesis-/
example {u : Type*} (A B C : Set u) : A Δ C ⊆ (A Δ B) ∪ (B Δ C) := by
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

/- a little bit of everything-/
example {u : Type*} (A B C : Set u) : C ⊆ A Δ B ↔ (C ⊆ A ∪ B ∧ (A ∩ B ∩ C = ∅)) := by
  constructor
  intro hC
  constructor
  intro c hc
  obtain ⟨hcA,hcB'⟩ | ⟨hcB,hcA'⟩ := hC hc
  left
  exact hcA
  right
  exact hcB
  rw[set_eq_iff]
  intro x
  constructor
  intro hx
  obtain this | that := hC hx.right
  exact this.right hx.left.right -- negated statements are weird
  exact that.right hx.left.left
  intro F
  contradiction
  intro ⟨h₁,h₂⟩ c hc
  by_cases ha : c ∈ A
  left
  refine ⟨ha,?_⟩
  by_contra! hb
  obtain F : c ∈ A ∩ B ∩ C := And.intro (And.intro ha hb) hc
  rw[h₂] at F
  exact F
  right
  refine ⟨?_,ha⟩
  obtain F | hb := h₁ hc
  contradiction
  exact hb

/- contradiction, emptyset problem-/
example {u : Type*} (A B C : Set u) : A ∩ C = ∅ → A \ (B \ C) ⊆ (A \ B) \ C := by
  intro h x ⟨hxA,hxBC⟩
  refine ⟨⟨hxA,?_⟩,?_⟩
  rw[mem_diff_iff] at hxBC
  rw[Not_and] at hxBC
  obtain hxB' | hxC := hxBC
  exact hxB'
  rw[Not_not] at hxC
  obtain hxAC : x ∈ A ∩ C := And.intro hxA hxC
  rw[h] at hxAC
  contradiction
  rw[mem_diff_iff] at hxBC
  rw[Not_and] at hxBC
  obtain hxB' | hxC := hxBC
  by_contra! F
  obtain hxAC : x ∈ A ∩ C := And.intro hxA F
  rw[h] at hxAC
  contradiction
  rw[Not_not] at hxC
  obtain hxAC : x ∈ A ∩ C := And.intro hxA hxC
  rw[h] at hxAC
  contradiction

/- existence/uniqueness problem -/
example {u : Type*} (U : Set u) : ∃! I ⊆ U, ∀ A ⊆ U, A Δ I = A := by
  exist! ∅
  constructor
  intro x hx
  contradiction
  -- apply Set.empty_subset -- this works instead of intro/contradiction
  intro A hA
  rw[set_eq_iff]
  intro x
  refine ⟨?_,?_⟩
  intro hx
  obtain ⟨hxA,F'⟩ | ⟨F,hxA'⟩ := hx
  exact hxA
  contradiction
  intro hxA
  left
  refine ⟨?_,?_⟩
  exact hxA
  by_contra!
  contradiction
  intro I hI
  by_contra!
  obtain ⟨i,hi⟩ := this
  obtain F := hI.right I hI.left
  rw[← F] at hi
  rw[Symm_diff_self] at hi
  contradiction

/- same -/
example {u : Type*} (U : Set u) : ∀ A ⊆ U, ∃! B ⊆ U, A Δ B = ∅ := by
  intro A hA
  exist! A
  refine ⟨hA,Symm_diff_self⟩
  intro B hB
  rw[set_eq_iff]
  intro x
  refine ⟨?_,?_⟩
  intro hxB
  by_contra!
  obtain that : x ∈ A Δ B
  right
  exact And.intro hxB this
  rw[hB.right] at that
  contradiction
  intro hxA
  by_contra!
  obtain that : x ∈ A Δ B
  left
  exact And.intro hxA this
  rw[hB.right] at that
  contradiction

example {u : Type*} (F G H : Set (Set u)) : (∀ A ∈ F, ∀ B ∈ G, A ∪ B ∈ H) → ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := by
  intro h x hx
  by_cases hF : x ∈ ⋂₀ F
  left
  exact hF
  right
  rw[mem_finter_iff]
  intro B hB
  --change ¬ x ∈ ⋂₀ F at hF --real confusing: internally things changed but the terminal delaborates the same way
  rw[mem_finter_iff] at hF
  push_neg at hF
  obtain ⟨ A, hA,hxA'⟩ := hF
  obtain hAB := h A hA B hB
  obtain hxA | hxB := hx (A ∪ B) hAB
  contradiction
  exact hxB
