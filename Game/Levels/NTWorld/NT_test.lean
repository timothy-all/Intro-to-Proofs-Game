import Game.Metadata
import Game.Levels.NTWorld.L01_NT
--import Mathlib.Tactic.Cases


structure GCD (a b : ℕ) where
  (g : Nat)
  (left_zero : a = 0 → g = b)
  (right_zero : b = 0 → g = a)
  (dvd_left : g ∣ a)
  (dvd_right : g ∣ b)
  (le : ¬(a = 0 ∧ b = 0) → ∀ d : ℕ , d ∣ a → d ∣ b → d ≤ g)

structure DIVALG (a b : ℕ) where
  (q : ℕ)
  (r : ℕ)
  (eq : a = b * q + r)
  (le : 0 ≤ r)
  (lt : 0 < b → r < b)

noncomputable def divalg (a b : ℕ) : DIVALG a b := by
  by_cases hb : b = 0
  refine
  { q := 0
    r := a
    eq := by
      simp
    le := by
      simp
    lt := by
      intro F
      rw[hb] at F
      contradiction}
  obtain ltb := Nat.zero_lt_of_ne_zero hb
  by_cases ha : a = 0
  refine
  { q := 0
    r := 0
    eq := by
      rw[ha]
      simp
    le := by
      rfl
    lt := by
      simp}
  obtain lta := Nat.zero_lt_of_ne_zero ha
  obtain spec := div_alg a b lta ltb
  let q := Classical.choose spec
  let q_spec := Classical.choose_spec spec
  let r := Classical.choose q_spec
  let r_spec := Classical.choose_spec q_spec
  refine
  { q := q
    r := r
    eq := r_spec.left
    le := r_spec.right.left
    lt := by
      intro hb
      exact r_spec.right.right}


def gcd (a b : ℕ) : GCD a b := by
  by_cases h : a = 0 ∧ b = 0
  refine
  { g := 0
    left_zero := by
      intro ha
      rw[h.right]
    right_zero := by
      intro hb
      rw[h.left]
    dvd_left := by
      rw[h.left]
    dvd_right := by
      rw[h.right]
    le := by
      intro F
      contradiction
  }
  refine
    { g := Nat.gcd a b
      left_zero := by
        intro ha
        rw[ha]
        exact Nat.gcd_zero_left b
      right_zero := by
        intro hb
        rw[hb]
        exact Nat.gcd_zero_right a
      dvd_left := by
        exact Nat.gcd_dvd_left a b
      dvd_right := by
        exact Nat.gcd_dvd_right a b
      le := by
        intro h' d hda hdb
        obtain le := Nat.dvd_gcd hda hdb
        apply Nat.le_of_dvd
        by_contra! F
        simp at F
        contradiction
        exact le
    }

theorem gcd_comm (a b : ℕ) (gab : GCD a b) (gba : GCD b a) : gab.g = gba.g := by
  by_cases h : a = 0 ∧ b = 0
  obtain ha := gba.right_zero h.left
  obtain hb := gab.right_zero h.right
  rw[ha,hb,h.left,h.right]
  obtain le := gab.le h gba.g gba.dvd_right gba.dvd_left
  rw[And_comm] at h
  obtain ge := gba.le h gab.g gab.dvd_right gab.dvd_left
  rw[Nat.eq_iff_le_and_ge]
  exact And.intro ge le

theorem gcd_eq (a b q r : ℕ) (gab : GCD a b) (gbr : GCD b r) (eq : a = b * q + r) : gab.g = gbr.g := by
  by_cases h : a = 0 ∧ b = 0
  rw[h.left,h.right,Nat.zero_mul,Nat.zero_add] at eq
  obtain hab := gab.left_zero h.left
  symm at eq
  obtain hbr := gbr.right_zero eq
  rw[hab,hbr]
  obtain hr : gab.g ∣ r
  obtain ⟨k,hk⟩ := gab.dvd_left
  obtain ⟨j,hj⟩ := gab.dvd_right
  use k - j * q
  rw[Nat.mul_sub,
    ← hk,
    ← Nat.mul_assoc,
    ← hj]
  grind -- weird, grind only works now
  by_cases h' : b = 0 ∧ r = 0
  grind
  obtain le := gbr.le h' gab.g gab.dvd_right hr
  obtain ha : gbr.g ∣ a
  obtain ⟨k,hk⟩ := gbr.dvd_left
  obtain ⟨j,hj⟩ := gbr.dvd_right
  use k * q + j
  grind -- must be because of the subtraction?
  obtain ge := gab.le h gbr.g ha gbr.dvd_left
  rw[Nat.eq_iff_le_and_ge]
  exact And.intro le ge

noncomputable def euclid (a b : ℕ) : ℕ :=
  if a = 0 then
    b
  else
  if b = 0 then
    a
  else
    euclid b (divalg a b).r
  termination_by b
  decreasing_by
    rename_i hb
    apply Nat.zero_lt_of_ne_zero at hb
    exact (divalg a b).lt hb

theorem divalg_zero_right (a : ℕ) : (divalg a 0).r = a := by
  rw[divalg]
  split_ifs with h1 h2
  rfl
  nth_rewrite 4 [h2]
  rfl
  contradiction
  -- dsimp[divalg] one-shots this

theorem euclid_succ (a b : ℕ) : euclid (a + 1) b = euclid b (divalg (a + 1) b).r := by
  rw[euclid]
  split_ifs with h1 h2 h3 h4 h5
  contradiction
  contradiction
  rfl
  contradiction
  rw[h5]
  rw[divalg]
  split_ifs
  dsimp
  rw[euclid]
  split_ifs
  rfl
  contradiction
  rfl
