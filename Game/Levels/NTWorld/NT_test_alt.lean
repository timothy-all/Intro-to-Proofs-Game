import Game.Metadata
import Game.Levels.NTWorld.L01_NT
--import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith

/-
Nat.sub_lt_of_pos_le
Nat.zero_lt_of_ne_zero
Nat.eq_zero_of_le_zero
Nat.lt_irrefl
Nat.sub_self
Nat.not_lt
Nat.le_iff_lt_or_eq
Nat.add_sub_self_left
Nat.le_zero_eq
Nat.dvd_add
Nat.add_sub_assoc
Nat.le_of_lt
-/

theorem divalg (a b : ℕ) (hb : 0 < b) : ∃ q r : ℕ, a = b * q + r ∧ r < b := by
  induction' a using Nat.strongRecOn with n ih
  by_cases h : b ≤ n
  obtain ⟨q,r,eq,lt⟩ := ih (n - b) (Nat.sub_lt_of_pos_le hb h)
  use q+1,r
  refine ⟨?_,lt⟩
  calc
    n = n - b + b := by omega
    n - b + b = b * q + r + b := by omega
    b * q + r + b = b * (q + 1) + r := by linarith
  rw[Nat.not_le] at h
  use 0,n
  --grind kills it here
  refine ⟨?_,h⟩
  simplify

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

theorem div_alg_alt (a b : ℕ) : ∃ q : ℕ, a = b * q + rem a b := by
  induction' a using Nat.strongRecOn with n ih
  rw[rem]
  split_ifs with hb lt
  use 0
  simplify
  use 0
  simplify
  apply Nat.zero_lt_of_ne_zero at hb
  rw[Nat.not_lt] at lt
  obtain sub_lt := Nat.sub_lt_of_pos_le hb lt
  obtain ⟨q,eq⟩ := ih (n - b) sub_lt
  use q + 1
  calc
    n = n - b + b := by omega -- linarith doesn't work here
    _ = b * q + rem (n - b) b + b := by omega
    _ = b * (q + 1) + rem (n - b) b := by linarith -- omega doesn't work here!

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
  --grind kills it here
  apply Nat.zero_lt_of_ne_zero at hb
  rw[Nat.not_lt] at h
  exact ih (n - b) (Nat.sub_lt_of_pos_le hb h)

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
  --if a = 0 then
  --  b
  --else
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
  split_ifs with h1
  rfl
  contradiction

theorem euclid_zero_left (b : ℕ) : euclid 0 b = b := by
  rw[euclid]
  split_ifs with h1
  rw[h1]
  rw[rem]
  split_ifs with lt
  rw[euclid_zero_right]
  rw[Nat.zero_sub,rem_zero_left,euclid_zero_right]

theorem euclid_self (b : ℕ) : euclid b b = b := by
  rw[euclid]
  split_ifs with h
  rfl
  rw[rem_self,euclid_zero_right]

theorem euclid_rec (a b : ℕ) : euclid a b = euclid b (rem a b) := by
  rw[euclid]
  split_ifs with h
  rw[rem]
  split_ifs
  rw[h,euclid_zero_left]
  rfl

theorem euclid_comm (a b : ℕ) : euclid a b = euclid b a := by
  rw[euclid]
  split_ifs with hb
  rw[hb,euclid_zero_left]
  by_cases h : a < b
  rw[rem]
  split_ifs
  rfl
  rw[Nat.not_lt,Nat.le_iff_lt_or_eq] at h
  rcases h with lt | rfl
  nth_rewrite 2 [euclid]
  split_ifs with ha
  rw[rem]
  split_ifs with altb
  rw[ha,euclid_zero_right]
  rw[ha,Nat.zero_sub,rem_zero_left,euclid_zero_right]
  nth_rewrite 2 [rem]
  split_ifs
  rw[← euclid_rec]
  rw[euclid_self,rem_self,euclid_zero_right]

theorem euclid_induction {P : ℕ → ℕ → Prop} (a b : ℕ) (h : ∀ b, P 0 b) (ih : ∀ a b, 0 < a → P (rem b a) a → P a b) : P a b := by
  induction' a using Nat.strong_induction_on with x ix generalizing b
  by_cases hx : x = 0
  rw[hx]
  exact h b
  apply ih
  exact Nat.zero_lt_of_ne_zero hx
  exact ix (rem b x) (rem_lt_right b hx) x

theorem euclid_dvd (a b : ℕ) : euclid a b ∣ a ∧ euclid a b ∣ b := by
  induction' a,b using euclid_induction with x y z h ih
  constructor
  use 0
  simplify
  rw[euclid]
  split_ifs with h1
  rw[h1]
  rw[rem_zero_left,euclid_zero_right]
  refine ⟨?_,?_⟩
  rw[euclid_comm,← euclid_rec,euclid_comm] at ih
  exact ih.right
  rw[euclid_comm,← euclid_rec,euclid_comm] at ih
  exact rem_rec_bck z y (euclid y z) (And.intro ih.right ih.left)

theorem dvd_euclid {a b d: ℕ} (hd : d ∣ a ∧ d ∣ b) : d ∣ euclid a b := by
  induction' a,b using euclid_induction with x y z h ih
  rw[euclid_zero_left]
  exact hd.right
  rw[euclid_comm,← euclid_rec,euclid_comm] at ih
  rw[And_comm,rem_rec,And_comm] at hd
  exact ih hd

inductive Wilf : ℕ → ℕ → Prop
  | base1 : Wilf 1 0
  | base2 : Wilf 0 1
  | left (a b : ℕ) : Wilf a b → Wilf (b + a) b
  | right (a b : ℕ) : Wilf a b → Wilf a (b + a)

theorem Wilf_symm {a b : ℕ} : Wilf a b → Wilf b a := by
  intro h
  induction' h with m n _ ih m n _ ih
  exact Wilf.base2
  exact Wilf.base1
  rw[Nat.add_comm]
  exact Wilf.right n m ih
  rw[Nat.add_comm]
  exact Wilf.left n m ih

theorem Nat.add_lt {a b : ℕ} : a + b < b → False := by
  simp -- if we were tempted to avoid omega

theorem euclid_succ (a b : ℕ) : euclid (a + b) b = euclid a b := by
  induction' a using Nat.strongRecOn with n ih
  rw[euclid]
  split_ifs with hb
  rw[hb,euclid_zero_right]
  simplify
  rw[rem]
  split_ifs with lt
  -- use omega here instead of the next two lines
  apply Nat.add_lt at lt
  contradiction
  rw[Nat.add_sub_cancel,← euclid_rec]

example (a b : ℕ) : Wilf a b → euclid a b = 1 := by
  intro h
  induction' h with m n ih ih' m n ih ih'
  rw[euclid_zero_right]
  rw[euclid_zero_left]
  rw[Nat.add_comm]
  rw[euclid_succ]
  exact ih'
  rw[Nat.add_comm,euclid_comm,Nat.add_comm,euclid_succ]
  rw[euclid_comm,ih']

--Strong induction → WOP. Not too bad, especially if they have the proof in English to go with it
theorem WOP (S : Set Nat) (hS : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, a ≤ b := by
  obtain ⟨n,hn⟩ := hS
  induction' n using Nat.strong_induction_on with k hk
  by_cases c1 : ∀ b ∈ S, k ≤ b --Either k is the minimum, or it's not
  use k
  push_neg at c1
  obtain ⟨sm, ⟨hsmS,hsm⟩⟩ := c1 --Now sm is smaller, so we still find a minimum in S using SIH
  obtain ⟨min,⟨hminS,hmin⟩⟩ := hk sm hsm hsmS
  use min

-- there's gotta be a better way... but maybe this is too hard.
example (a b : ℕ) : euclid a b = 1 → Wilf a b := by
  let S := { x | ∃ a b : ℕ, x = a + b ∧ euclid a b = 1 ∧ ¬ Wilf a b}
  by_cases hS : S.Nonempty
  apply WOP at hS
  rcases hS with ⟨m,⟨⟨x,⟨y,⟨eq,exy,nW⟩⟩⟩,hmin⟩⟩
  by_cases lt : x < y -- this is really the only case
  let y' := y - x
  obtain t1 := euclid_dvd x (y - x)
  obtain t2 := Nat.dvd_add t1.right t1.left
  obtain le := Nat.le_of_lt lt
  rw[Nat.sub_add_cancel le] at t2
  obtain t3 := dvd_euclid (And.intro t1.left t2)
  rw[exy] at t3
  rw[Nat.dvd_one] at t3
  obtain W : Wilf x (y - x)
  by_contra F
  obtain hy : y ∈ S
  use x, (y - x)
  refine ⟨?_,t3,F⟩
  rw[Nat.add_sub_cancel' le]
  obtain F' := hmin y hy
  rw[eq] at F'
  rw[Nat.le_iff_lt_or_eq] at F'
  rcases F' with F1' | F2'
  omega
  rw[Nat.add_eq_right] at F2'
  rw[F2',euclid_zero_left] at exy
  rw[F2',exy] at nW
  exact nW Wilf.base2
  obtain F := Wilf.right x (y - x) W
  rw[Nat.sub_add_cancel le] at F
  contradiction
  rw[Nat.not_lt,Nat.le_iff_lt_or_eq] at lt
  rcases lt with lt | rfl
  let x' := x - y
  obtain t1 := euclid_dvd (x - y) y
  obtain t2 := Nat.dvd_add t1.right t1.left
  obtain le := Nat.le_of_lt lt
  rw[Nat.add_sub_cancel' le] at t2
  obtain t3 := dvd_euclid (And.intro t2 t1.right)
  rw[exy] at t3
  rw[Nat.dvd_one] at t3
  obtain W : Wilf (x - y) y
  by_contra F
  obtain hx : x ∈ S
  use (x - y), y
  refine ⟨?_,t3,F⟩
  rw[Nat.sub_add_cancel le]
  obtain F' := hmin x hx
  rw[eq] at F'
  rw[Nat.le_iff_lt_or_eq] at F'
  rcases F' with F1' | F2'
  omega
  rw[Nat.add_eq_left] at F2'
  rw[F2',euclid_zero_right] at exy
  rw[F2',exy] at nW
  exact nW Wilf.base1
  obtain F := Wilf.left (x - y) y W
  rw[Nat.add_sub_cancel' le] at F
  contradiction
  rw[euclid_self] at exy
  rw[exy] at nW
  obtain nW' := Wilf.left 0 1 Wilf.base2
  rw[Nat.add_zero] at nW'
  contradiction
  rw[Set.Nonempty] at hS
  intro h
  let x := a + b
  by_contra! F
  obtain xS : x ∈ S
  use a,b
  push_neg at hS
  obtain F' := hS x
  contradiction

inductive Far : ℕ → ℕ → Prop
  | base1 : Far 0 1
  | base2 : Far 1 1
  | succ (a b c d : ℕ) : Far a b → Far c d → a * d - b * c = 1 → Far (a + c) (b + d)

example (a b : ℕ) : Far a b → euclid a b = 1 := by
  intro h
  induction' h with x y z w ih1 ih2 eq exy ezw
  rw[euclid_zero_left]
  rw[euclid_self]
  obtain eq : w * (x + z) - z * (y + w) = 1 := by grind -- gurr
  obtain hxy := euclid_dvd (x + z) (y + w)
  obtain hxw := Nat.dvd_mul_left_of_dvd hxy.left w
  obtain hyz := Nat.dvd_mul_left_of_dvd hxy.right z
  obtain this := Nat.dvd_sub hxw hyz
  rw[eq,Nat.dvd_one] at this
  exact this

-- try to make extended euclid work computationally
