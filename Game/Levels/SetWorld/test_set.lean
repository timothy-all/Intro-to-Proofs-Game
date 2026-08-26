import Game.Levels.SetWorld.L12_set

open Set

example {u : Type*} (A B: Set u) (h : A.Nonempty) :  A ⊆ B → B.Nonempty :=  by
  intro hAB
  obtain ⟨x,hx⟩ := h
  rw[Set.Nonempty]
  use x
  exact hAB hx

example {u: Type*} (A: Set u) : ∅ ⊆ A := by
  intro x hx
  contradiction

example {u: Type*} (x : u) : x ∈ univ := by
  --rw[mem_univ_iff_true]
  exact True.intro -- like And.intro


/- Proof world example -/
example {u : Type*} (A : Set u) : A = ∅ ↔ ∀ {x}, x ∉ A := by
  constructor
  intro h x
  by_contra! F
  rw[h] at F
  exact F
  intro h
  rw[set_eq_iff]
  intro y
  constructor
  intro hy
  exact h hy
  intro F
  contradiction

example {u : Type*} (A : Set u) : A.Nonempty ↔ ∃ x, x ∈ A := by
  rfl -- ok, so this is the literal def

theorem test {u : Type*} (A : Set u) : A ≠ ∅ ↔ A.Nonempty := by
  --push_neg (try not use this)
  constructor
  rw[Contrapositive]
  rw[Not_not]
  intro h
  rw[Set.Nonempty] at h
  rw[Not_exists] at h
  rw[set_eq_iff]
  intro x
  constructor
  intro hx
  exact h x hx
  intro F
  contradiction
  rw[Contrapositive]
  rw[Not_not]
  intro h
  rw[Set.Nonempty]
  rw[Not_exists]
  intro x
  by_contra!
  rw[h] at this
  contradiction

theorem test2 {u : Type*} (A : Set u) : ¬ A.Nonempty ↔ A = ∅ := by
  --rw[← test]
  --rw[Not_not] this kills it at this point
  constructor
  intro h
  rw[Set.Nonempty,Not_exists] at h
  rw[set_eq_iff]
  intro x
  constructor
  intro hx
  exact h x hx
  intro F
  contradiction
  intro h
  rw[Set.Nonempty]
  rw[Not_exists]
  intro x
  by_contra!
  rw[h] at this
  contradiction


example {u : Type*} (A B : Set u) (hAB : A ⊆ B) (hBA : B ⊆ A): A = B := by
  rw[set_eq_iff]
  intro x
  constructor
  intro hxA
  exact hAB hxA
  intro hxB
  exact hBA hxB
