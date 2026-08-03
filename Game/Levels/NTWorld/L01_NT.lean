import Game.Metadata
import Game.Levels.InductionWorld
--import Mathlib.Tactic.Cases


World "NTWorld"
Level 1

Title "Level 1"

Introduction "Here goes nothing."

/--
The division algorith, sucka.
-/
TheoremDoc div_alg as "NT: div_alg"

Statement div_alg (a b : ℕ) (ha : 0 = a ∨ 0 < a) (hb : 0 < b) : ∃ q r : ℕ, a = b * q + r ∧ 0 ≤ r ∧ r < b := by
  rcases ha with rfl | lt
  use 0,0
  refine ⟨?_,?_,hb⟩
  simplify
  rfl
  induction' a using Nat.strong_induction_on with n ih
  by_cases hn : b < n
  obtain sub_lt : n - b < n := Nat.sub_lt lt hb
  obtain pos : 0 < n - b := Nat.sub_pos_of_lt hn
  obtain ⟨q,⟨r,eq,le,lt⟩⟩ := ih (n-b) sub_lt pos
  use (q+1),r -- the hard part
  refine ⟨?_,le,lt⟩
  rw[Nat.mul_add,
    Nat.add_comm (b * q),
    Nat.add_assoc,
    ← eq,
    Nat.mul_one,
    Nat.add_comm,
    Nat.sub_add_cancel
    ] -- grind also works
  exact Nat.le_of_lt hn
  rw[Nat.not_lt] at hn
  rw[Nat.le_iff_lt_or_eq] at hn
  cases hn
  use 0,n
  refine ⟨?_,Nat.le_of_lt lt,h⟩
  simplify
  use 1,0
  refine ⟨?_,?_,hb⟩
  rw[h]
  simplify
  rfl

Conclusion "A pithy conclusion."
