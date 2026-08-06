import Game.Metadata
import Game.Levels.NTWorld.L01_NT
--import Mathlib.Tactic.Cases

def rem (a b : ℕ) : ℕ :=
  if b = 0 then
    a
  else
  if a < b then
    a
  else
    rem (a - b) b
  termination_by a
  decreasing_by
    rename_i ha
    rename_i hb
    apply Nat.zero_lt_of_ne_zero at hb
    simp at ha
    exact Nat.sub_lt_of_pos_le hb ha

theorem rem_zero_right (a : ℕ) : rem a 0 = a := by
  rw[rem]
  split_ifs with h1 h2
  rfl
  contradiction
  contradiction

theorem rem_zero_left (b : ℕ) : rem 0 b = 0 := by
  rw[rem]
  split_ifs with h1 h2
  rfl
  rfl
  rw[Nat.not_lt] at h2
  apply Nat.eq_zero_of_le_zero at h2
  contradiction

theorem rem_self (a : ℕ) : rem a a = 0 := by
  rw[rem]
  split_ifs with h1 h2
  exact h1
  apply Nat.lt_irrefl at h2
  contradiction
  rw[Nat.sub_self,rem_zero_left]

theorem rem_lt_right {b : ℕ} (a : ℕ) : ¬ (b = 0) → rem a b < b := by
  intro hb
  induction' a using Nat.strong_induction_on with n ih
  rw[rem]
  split_ifs with h
  exact h
  apply Nat.zero_lt_of_ne_zero at hb
  rw[Nat.not_lt] at h
  exact ih (n - b) (Nat.sub_lt_of_pos_le hb h)

theorem rem_lt_left (a b : ℕ) (h : b ≠ 0) (lt : b < a) : rem a b < a := Nat.lt_trans (rem_lt_right a h) lt

theorem rem_rec_fwd (a b d : ℕ) (hd : d ∣ a ∧ d ∣ b) : d ∣ rem a b := by
  induction' a using Nat.strong_induction_on with n ih
  rw[rem]
  split_ifs with hb lt
  exact hd.left
  exact hd.left
  rw[Nat.not_lt,Nat.le_iff_lt_or_eq] at lt
  rcases lt with lt | rfl
  apply Nat.zero_lt_of_ne_zero at hb
  apply Nat.le_of_lt at lt
  obtain sub_lt := Nat.sub_lt_of_pos_le hb lt
  obtain dvd_sub := Nat.dvd_sub hd.left hd.right
  exact ih (n - b) sub_lt (And.intro dvd_sub hd.right)
  rw[Nat.sub_self,rem_zero_left]
  use 0
  simplify

theorem rem_rec_bck (a b d : ℕ) (hd : d ∣ b ∧ d ∣ rem a b) : d ∣ a := by
  induction' a using Nat.strong_induction_on with n ih
  rw[rem] at hd
  split_ifs at hd with hb lt
  exact hd.right
  exact hd.right
  rw[Nat.not_lt,Nat.le_iff_lt_or_eq] at lt
  rcases lt with lt | rfl
  apply Nat.zero_lt_of_ne_zero at hb
  apply Nat.le_of_lt at lt
  obtain sub_lt := Nat.sub_lt_of_pos_le hb lt
  obtain dvd_sub := ih (n - b) sub_lt (And.intro hd.left hd.right)
  obtain dvd_add := Nat.dvd_add hd.left dvd_sub
  rw[← Nat.add_sub_assoc, Nat.add_sub_self_left] at dvd_add
  exact dvd_add
  exact lt
  exact hd.left

theorem rem_rec (a b d : ℕ) : (d ∣ a ∧ d ∣ b) ↔ (d ∣ b ∧ d ∣ rem a b) := by
  constructor
  intro hd
  refine ⟨hd.right,?_⟩
  exact rem_rec_fwd a b d hd
  intro hd
  refine ⟨?_,hd.left⟩
  exact rem_rec_bck a b d hd

def euclid (a b : ℕ) : ℕ :=
  if a = 0 then
    b
  else
  if b = 0 then
    a
  else
    euclid b (rem a b)
  termination_by b
  decreasing_by
    rename_i hb
    exact rem_lt_right a hb

theorem euclid_zero_right (a : ℕ) : euclid a 0 = a := by
  rw[euclid]
  split_ifs with h1 h2
  rw[h1]
  rfl
  contradiction

theorem euclid_zero_left (b : ℕ) : euclid 0 b = b := by
  rw[euclid]
  split_ifs with h1 h2
  rfl
  rw[h2]
  contradiction

theorem euclid_self (b : ℕ) : euclid b b = b := by
  rw[euclid]
  split_ifs with h
  rfl
  rw[rem_self,euclid_zero_right]

theorem euclid_rec (a b : ℕ) : euclid a b = euclid b (rem a b) := by
  rw[euclid]
  split_ifs with h1 h2
  rw[rem]
  split_ifs with h1b h2b
  repeat rw[h1,euclid_zero_right]
  rw[Nat.not_lt,h1,Nat.le_zero_eq] at h2b
  contradiction
  rw[h2,euclid_zero_left,rem_zero_right]
  rfl

theorem euclid_comm (a b : ℕ) : euclid a b = euclid b a := by
  rw[euclid]
  split_ifs with h1 h2
  rw[h1,euclid_zero_right]
  rw[h2,euclid_zero_left]
  by_cases h : a < b
  rw[rem]
  split_ifs
  rfl
  rw[Nat.not_lt,Nat.le_iff_lt_or_eq] at h
  rcases h with lt | rfl
  nth_rewrite 2 [euclid]
  split_ifs
  nth_rewrite 2 [rem]
  split_ifs
  nth_rewrite 2 [euclid_rec]
  rfl
  rw[euclid_self,rem_self,euclid_zero_right]

theorem weird_induction {P : ℕ → ℕ → Prop} (a b : ℕ) (h : ∀ b, P 0 b) (ih : ∀ a b, 0 < a → P (rem b a) a → P a b) : P a b := by
  induction' a using Nat.strongRecOn with x ix generalizing b
  by_cases hx : x = 0
  rw[hx]
  exact h b
  apply ih
  exact Nat.zero_lt_of_ne_zero hx
  exact ix (rem b x) (rem_lt_right b hx) x

theorem euclid_dvd (a b : ℕ) : euclid a b ∣ a ∧ euclid a b ∣ b := by
  induction' a,b using weird_induction with x y z h ih
  constructor
  use 0
  simplify
  rw[euclid]
  split_ifs with h1 h2
  rfl
  contradiction
  contradiction
  refine ⟨?_,?_⟩
  rcases ih with ⟨ih1,ih2⟩
  rw[euclid_comm,← euclid_rec,euclid_comm] at ih2
  exact ih2
  rcases ih with ⟨ih1,ih2⟩
  rw[euclid_comm,← euclid_rec,euclid_comm] at ih1 ih2
  exact rem_rec_bck z y (euclid y z) (And.intro ih2 ih1)

theorem dvd_euclid (a b d: ℕ) (hd : d ∣ a ∧ d ∣ b) : d ∣ euclid a b := by
  induction' a,b using weird_induction with x y z h ih
  rw[euclid_zero_left]
  exact hd.right
  rw[euclid_comm,← euclid_rec,euclid_comm] at ih
  rw[And_comm,rem_rec,And_comm] at hd
  exact ih hd

theorem rem_bezout (a b : ℕ) : ∃ q : ℕ, a - b * q = rem a b := by
  induction' a using Nat.strongRecOn with n ih
  rw[rem]
  split_ifs with hb lt
  use 0
  rw[Nat.mul_zero,Nat.sub_zero]
  use 0
  rw[Nat.mul_zero,Nat.sub_zero]
  apply Nat.zero_lt_of_ne_zero at hb
  rw[Nat.not_lt] at lt
  obtain sub_lt := Nat.sub_lt_of_pos_le hb lt
  obtain ⟨q,eq⟩ := ih (n - b) sub_lt
  use q + 1
  grind

theorem bezout (a b : ℕ) : ∃ x y : ℕ, a * x - b * y = euclid a b := by
  sorry
