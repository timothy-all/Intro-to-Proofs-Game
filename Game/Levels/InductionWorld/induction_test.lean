import Game.Levels.InductionWorld.L02_Induction

/-Lines below set up sigma notation-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith

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

/-
- Exponential problems with only +'s
-- HTPIwL has problems involving subtraction but everything is explicitly casted to Ints
- Strong induction
-/

--Divisibility example
example (n : Nat) : 64 ∣ 9^n - 8*n - 1:= by
  induction' n with k ih
  use 0
  simplify
  obtain ⟨l, hl⟩ := ih
  use 9*l+k
  --Simplify does NOT close the goal from here, which might be reasonable because it still has l
  rw [mul_add 64, ← mul_assoc, mul_comm 64, mul_assoc, ← hl]
  zify
  norm_cast
  push_cast


  --Even with l removed, simplify still doesn't close it. Doing `pow_succ` afterward doesn't help, maybe the issue is the fact that there are more exponent rules required to solve it.
  sorry


--Divisibility example reattempt
example (n : Nat) : 64 ∣ 9^n + 56*n + 63 := by --Changed to only have +
  induction' n with k ih
  use 1
  simplify
  obtain ⟨l, hl⟩ := ih
  obtain h : 9*l-7*k-7 ≥ 0 := by sorry
  use 9*l-7*k-7 --even changing original problem to have + doesn't avoid using -? Now sub_sub would be needed to simplify here and it doesn't work again
  --Simplify does NOT close the goal from here, which might be reasonable because it still has l
  --rw [mul_add 64, ← mul_assoc, mul_comm 64, mul_assoc, ← hl]
  zify [h]
  push_cast


  --Even with l removed, simplify still doesn't close it. Doing `pow_succ` afterward doesn't help, maybe the issue is the fact that there are more exponent rules required to solve it.
  sorry


--Recursion testing
--Recursively defined function below
def testrec : Nat → Int
  | 0 => 0
  | n+1 => 2 * (testrec n) + n

--Original example below
example (n : Nat) : testrec n = (2^n) - n - 1 := by
  induction' n with k ih
  --simplify does not immediately work, have to remove testrec first
  rw [testrec]
  simplify --adding push_cast to simplify broke this
  --tutorialization on `rw [testrec]` is needed to show how to apply recursion
  rw [testrec, ih]--, sub_sub,mul_sub,mul_comm,← pow_succ]
  ring_nf!

    --this isn't close enough for simplify to resolve
  --rw [pow_succ]--sub_sub (2^k) k 1] --<- the sub_sub here doesn't work, why? Doesn't work in reverse to work with 2^k*2-(k+1) either
  --I think there's some kind of issue with ℕ not being closed under subtraction...
  --linarith
  sorry



--push_cast attempt
example (n : Nat) : testrec n = (2^n) - n - 1 := by
  induction' n with k ih
  rw [testrec]
  simplify
  --tutorialization on `rw [testrec]` is needed to show how to apply recursion
  rw [testrec, ih]--, sub_sub,mul_sub,mul_comm,← pow_succ]
  push_cast --Is this the key?
  simplify
Conclusion " "


--Below is an example that is simple enough to actually work. Doesn't get more basic than this. Stuff too much more complicated than this might not even be worth doing
def testrec2 : Nat → Nat
  | 0 => 0
  | n+1 => 2 * (testrec2 n) + 2^(n+1)

example (n:Nat) : testrec2 n = n*2^n := by
  induction' n with k ih
  rw [testrec2]
  simplify
  rw [testrec2,ih]
  simplify


--Strong induction example
def myfib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => myfib (n+1) + myfib (n)

example (m n:Nat) : myfib (m+n+1) = myfib (m) * myfib (n) + myfib (m+1) * myfib (n+1) := by
  induction' n using Nat.strong_induction_on with k sih --We could rename Nat.strong_induction_on to be "strong induction" or something
  --Separate out the k = 0 and k = 1 cases so we can apply the SIH properly. Applications of the omega tactic require these
  by_cases bc0:k = 0
  rw [bc0]
  repeat rw [myfib]
  simplify
  by_cases bc1:k = 1
  rw [bc1]
  repeat rw [myfib]
  simplify
  obtain sihkm1 := sih (k-1)
  obtain sihkm2 := sih (k-2)
  obtain temp1 : k - 1 < k := by omega --These temps become what we get out of the SIH
  obtain temp2 : k - 2 < k := by omega
  apply sihkm1 at temp1
  apply sihkm2 at temp2
  --What's below begs for a calc-style proof, I just haven't done any of those. I'm guessing they don't work with the game either, but one nightmare later it's proven
  obtain simp1 : m+k+1 = (m+(k-1))+2 := by omega --The -1 can't be associated with m because you can't prove m-1 ∈ ℕ
  rw [simp1, myfib]
  obtain simp2 : m+(k-1) = m+(k-2)+1 := by omega
  nth_rw 2 [simp2]
  rw [temp1,temp2]
  obtain simp4 : k-2+1 = k-1 := by omega
  obtain simp5 : k-1+1 = k := by omega
  obtain simp3 : myfib m * myfib (k - 1) + myfib (m + 1) * myfib (k - 1 + 1) +
    (myfib m * myfib (k - 2) + myfib (m + 1) * myfib (k - 2 + 1)) = (myfib m) * (myfib (k - 1) + myfib (k - 2)) + (myfib (m + 1)) * (myfib (k - 1) + myfib k) := by
    rw [simp4,simp5]
    simplify
  obtain simp6 : k = (k-2)+2 := by omega
  obtain simp7 : k+1 = (k-1)+2 := by omega
  rw [simp3]
  nth_rw 5 [simp6]
  nth_rw 1 [simp7]
  rw [myfib,myfib,simp4,simp5]
  simplify




--From AI, doing this with "match." Doesn't check currently but might be a good alternative SI method?
/-
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    match n with
    | 0 =>
      -- fib(m + 0 + 1) = fib(m+1)
      -- RHS = fib(m)*fib(0) + fib(m+1)*fib(1) = 0 + fib(m+1)*1
      simp [fib]
    | 1 =>
      -- fib(m + 2) = fib(m)*1 + fib(m+1)*1
      simp [fib, fib_add_two]
      ring
    | (n + 2) =>
      -- Strong IH gives us the result for n and n+1
      have ih1 : fib (m + n + 1) = fib m * fib n + fib (m+1) * fib (n+1) :=
        ih n (by omega)
      have ih2 : fib (m + (n+1) + 1) = fib m * fib (n+1) + fib (m+1) * fib (n+2) :=
        ih (n+1) (by omega)
      -- Now combine: fib(m + (n+2) + 1) = fib(m + n + 2) + fib(m + n + 3)
      have key : m + (n + 2) + 1 = (m + n + 1 + 1) + 1 := by omega
      rw [key, fib_add_two]
      -- Rewrite ih1 and ih2 with adjusted indices
      have lhs_eq : m + n + 1 + 1 = m + (n + 1) + 1 := by omega
      rw [lhs_eq, ih2, ih1]
      simp [fib_add_two]
      ring
-/
