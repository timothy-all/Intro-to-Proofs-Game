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
-/


def quo (a b : ℕ) : ℕ :=
  if b = 0 then
    0
  else
  if a < b then
    0
  else
    quo (a - b) b + 1
  termination_by a
  decreasing_by
    rename_i h
    rename_i hb
    rw[Nat.not_lt] at h
    apply Nat.zero_lt_of_ne_zero at hb
    exact Nat.sub_lt_of_pos_le hb h

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

theorem divalg_eq (a b : ℕ) : a = b * quo a b + rem a b := by
  induction' a using Nat.strongRecOn with n ih
  rw[quo,rem]
  split_ifs with hb lt
  repeat grind -- whoa! maybe this is a good reason not to do things this way?

def ext_rem (a b : ℕ) : ℕ → ℕ
  | 0 => b
  | 1 => rem a b
  | n + 2 => rem (ext_rem a b n) (ext_rem a b (n+1))

def ext_quo (a b : ℕ) : ℕ → ℕ
  | 0 => b
  | 1 => quo a b
  | n + 2 => quo (ext_rem a b n) (ext_rem a b (n+1))

def pn (a b : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => pn a b n + pn a b (n+1) * ext_quo a b (n + 1)

def qn (a b : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | n + 2 => qn a b n + qn a b (n+1) * ext_quo a b (n + 1)

#eval 19 * qn 19 12 1 - 12 * pn 19 12 1
#eval ext_rem 19 12 0



-- try to make extended euclid work computationally
