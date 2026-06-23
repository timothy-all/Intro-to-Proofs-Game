import Game.Levels.InductionWorld.L02_Induction

/-Lines below set up sigma notation-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
open Finset
open BigOperators


World "InductionWorld"
Level 3

Title "Basic Induction"

Introduction "."

--Placeholder level
Statement (n : Nat) : ∑ k ∈ range (n+1), 2*k = n*(n+1) := by
  sorry


Conclusion " "

--Divisibility example
example (n : Nat) : 64 ∣ 9^n - 8*n - 1 := by
  induction' n with k ih
  use 0
  simplify
  obtain ⟨l, hl⟩ := ih
  use 9*l+k
  --Simplify does NOT close the goal from here, which might be reasonable because it still has l
  rw [mul_add 64, ← mul_assoc, mul_comm 64, mul_assoc, ← hl]
  --Even with l removed, simplify still doesn't close it. Doing `pow_succ` afterward doesn't help, maybe the issue is the fact that there are more exponent rules required to solve it.
  simplify
  sorry


--Recursion testing
--Recursively defined function below
def testrec : Nat → Nat
  | 0 => 0
  | n+1 => 2 * (testrec n) + n


example (n : Nat) : testrec n = (2^n) - n - 1 := by
  induction' n with k ih
  --simplify does not immediately work, have to remove testrec first
  rw [testrec]
  simplify
  --tutorialization on `rw [testrec]` is needed to show how to apply recursion
  rw [testrec, ih]
  --this isn't close enough for simplify to resolve
  rw [pow_succ]--sub_sub (2^k) k 1] <- the sub_sub here doesn't work, why? Doesn't work in reverse to work with 2^k*2-(k+1) either
  --I think there's some kind of issue with ℕ not being closed under subtraction...
  simplify
  sorry

Conclusion " "
