import Game.Levels.SetWorld
import Game.Levels.SetWorld.SetWorld_eg
import Game.Levels.PfWorld.Metadata_pfworld
import Game.Levels.PfWorld.pf_docs

open Set

/- destructuring exists with obtain? (done, L04_quant), simplify...direct proof I guess -/
example (x y : Int) (hx : isEven x) (hy: isEven y) : isEven (x + y) := by
  rw[isEven] at hx hy
  obtain ⟨k,hk⟩ := hx
  obtain ⟨l,hl⟩ := hy
  exist k+l
  rw[hk,hl]
  simplify

/- another direct proof-/
example (n : Int) : isOdd n → Divides 4 (n^2-1) := by
  intro h
  obtain ⟨k,hk⟩ := h
  exist k^2 + k
  rw[hk]
  simplify

/- classic contrapose-/
example (x : Int) : ¬ isEven (x ^ 2) → ¬ isEven x := by
  contrapose!
  intro h
  rw[isEven] at h ⊢
  obtain ⟨k,hk⟩ := h
  use 2 * k ^ 2
  rw[hk]
  simplify

/-contrapose!, indirect proof example-/
example (x y : Int) : ¬ isOdd (x * y) → ¬ (isOdd x ∧ isOdd y) := by
  contrapose!
  intro h
  rw[isOdd]
  obtain ⟨⟨c,hc⟩,⟨d,hd⟩⟩ := h
  exist 2* c * d + c + d
  rw[hc,hd]
  simplify

/- contrapose, indirect proof-/
example (u : Type*) (A B C D : Set u) (h : A ∩ B ⊆ C \ D) (x : u) : x ∈ A → (x ∈ D → x ∉ B) := by
  intro hxA
  contrapose
  rw[Not_not]
  intro hxB
  obtain want := h (And.intro hxA hxB)
  exact want.right

/- Proof by contradiction, by_contra and contradiction tactics-/
example (P Q R : Prop) : (¬ R → (P → ¬ Q)) → (P → (Q → R)) := by
  intro h hP hQ
  by_contra F
  obtain hQ' := h F hP
  contradiction

/- quantifier proof, constructor, proof of conjunction, exist -/
example : ∀ n : Int, Divides 21 n → ( Divides 7 n ∧ Divides 3 n) := by
  intro n h
  obtain ⟨k,hk⟩ := h
  constructor
  exist 3 * k
  rw[← hk]
  simplify
  exist 7 * k
  rw[← hk]
  simplify

/- quantifier proof, refine, apply -- maybe these should be separated-/
example (u : Type*) (F G : Set (Set u)) : ⋃₀ F ∩ ⋃₀ G ⊆ ⋃₀ (F ∩ G) ↔ ∀ A ∈ F, ∀ B ∈ G, A ∩ B ⊆ ⋃₀ (F ∩ G) := by
  constructor
  intro h A hA B hB x hx
  apply h
  constructor
  exist A
  refine ⟨hA,hx.left⟩
  exist B
  refine ⟨hB,hx.right⟩
  intro h x hx
  obtain ⟨A,hA,hxA⟩ := hx.left
  obtain ⟨B,hB,hxB⟩ := hx.right
  obtain hAB := h A hA B hB
  apply hAB
  exact And.intro hxA hxB

/- pf of iff statement -/
example (n : Int) : Divides 40 n ↔ (Divides 8 n ∧ Divides 5 n) := by
  constructor
  intro ⟨k,hk⟩
  constructor
  exist  5 * k
  rw[← hk]
  simplify
  exist  8 * k
  rw[← hk]
  simplify
  intro ⟨⟨k,hk⟩, ⟨j,hj⟩⟩
  obtain h1 : 15 * n = 120 * k
  rw[← hk]
  simplify
  obtain h2 : 16 * n = 80 * j
  rw[← hj]
  simplify
  obtain h3 : n = 80 * j - 120 * k
  rw[← h1,← h2]
  simplify
  exist  2*j - 3*k
  rw[h3]
  simplify

/- by_cases and proof using disjunction hypothesis, probably too difficult for tutorial world? -/
example (u : Type*) (A B : Set u) : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B → (A ⊆ B ∨ B ⊆ A) := by
  intro h
  rw[set_eq_iff] at h
  by_cases hAB : A ⊆ B
  left
  exact hAB
  right
  rw[subset_iff] at hAB
  rw[Not_forall] at hAB
  obtain ⟨a,ha⟩ := hAB
  rw[Imp_iff_not_or,Not_or,Not_not] at ha
  intro b hb
  obtain hab := h {a,b}
  obtain hab_left : {a,b} ∈ 𝒫 (A ∪ B)
  rw[mem_powerset_iff]
  intro x hx
  obtain xa | xb := hx
  left
  rw[xa]
  exact ha.left
  right
  rw[xb]
  exact hb
  rw[hab] at hab_left
  obtain T | F := hab_left
  rw[mem_powerset_iff] at T
  apply T
  right
  rfl
  obtain F' : a ∈ B
  rw[mem_powerset_iff] at F
  apply F
  left
  rfl
  obtain F'' := ha.right
  contradiction

/- proof using disjunctive hypothesis-/
example (u : Type*) (A B C : Set u) : A ∪ C = B ∪ C → (A \ B ∪ B \ A) ⊆ C := by
  intro h x hx
  obtain hxa | hxb := hx -- here
  obtain hxAC : x ∈ A ∪ C
  left
  exact hxa.left
  rw[h] at hxAC
  obtain hxB | hxC := hxAC
  obtain hxB' := hxa.right
  contradiction
  exact hxC
  obtain hxBC : x ∈ B ∪ C
  left
  exact hxb.left
  rw[← h] at hxBC
  obtain hxA | hxC := hxBC
  obtain hxA' := hxb.right
  contradiction
  exact hxC

/- existence and uniqueness proof-/
example : ∃! (d : Int), ∀ (x : Int), d * x = 0 := by
  exist! 0
  intro x
  simplify
  intro y h
  obtain h' := h 1
  rw[← h']
  simplify

/- another proof using disjunctive hypothesis-/
example {u : Type*} (A B C: Set u) (x : u) : x ∈ A Δ (B Δ C) → x ∈ A ∧ x ∈ B → x ∈ A ∩ B ∩ C := by
  intro hx hxab
  constructor
  exact hxab
  obtain ⟨_,t1⟩ | t2 := hx
  rw[mem_symm_diff_iff] at t1
  rw[mem_union_iff] at t1
  rw[Not_or] at t1
  rw[mem_diff_iff] at t1
  rw[Not_and] at t1
  rw[Not_not] at t1
  obtain this := t1.left
  rw[← Imp_iff_not_or] at this
  exact this hxab.right
  rw[mem_diff_iff] at t2
  obtain ⟨this,_⟩ := t2
  obtain ⟨that,_⟩ := hxab
  contradiction

/- another by_cases example -/
example {u : Type*} (A B C : Set u) (h : A Δ B ⊆ C) (hb : B ⊆ C) (hb' : Bᶜ ⊆ A): ∀ x, x ∈ C := by
  intro x
  by_cases hxb : x ∈ B
  exact hb hxb
  obtain hxa := hb' hxb
  obtain want : x ∈ A Δ B
  left
  exact And.intro hxa hxb
  exact h want
