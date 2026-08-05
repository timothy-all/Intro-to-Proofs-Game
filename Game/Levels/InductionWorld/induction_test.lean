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
  obtain h : 9*l-7*k-7 ≥ 0 := by omega
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
  push_cast --adding push_cast to simplify broke this
  --tutorialization on `rw [testrec]` is needed to show how to apply recursion
  rw [testrec, ih]--, sub_sub,mul_sub,mul_comm,← pow_succ]
  push_cast
  simplify


    --this isn't close enough for simplify to resolve
  --rw [pow_succ]--sub_sub (2^k) k 1] --<- the sub_sub here doesn't work, why? Doesn't work in reverse to work with 2^k*2-(k+1) either
  --I think there's some kind of issue with ℕ not being closed under subtraction...
  --linarith





--Below is an example that is simple enough to actually work. Doesn't get more basic than this. Stuff too much more complicated than this might not even be worth doing
def testrec2 : Nat → Nat
  | 0 => 0
  | n+1 => 2 * (testrec2 n) + 2^(n+1)

example (n:Nat) : testrec2 n = n*2^n := by
  induction' n with k ih
  rw [testrec2]
  simplify
  rw [add_comm]--,testrec2,ih] <- This worked at some point, I think, but stopped working?
  simplify
  sorry


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
  obtain simp1 : m+k+1 = ((m)+(k-1))+2 := by omega --The -1 can't be associated with m because you can't prove m-1 ∈ ℕ
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


--------------------------------------------------------------------------------------------------
--Work for 7/8 meeting


--Two variable induction. Seems easy enough
example {u v : Nat} (P: Nat → Nat → Prop) : P 0 0 → (∀ m n, P m n → P (m+1) n) → (∀ m n, P m n → P m (n+1)) → ∀ m n, P m n := by
  intro bc mih nih m n
  induction' m with k hk
  induction' n with l hl
  exact bc
  exact nih 0 l hl
  exact mih k n hk


--Induction → Strong induction. This can surely be drastically simplified, feels bad, but could possibly work for a level
example (P: Nat → Prop) : (∀ m, (∀ n < m, P n) → P m) → ∀ m, P m := by
  intro sih m
  apply sih m
  induction' m with k hk
  intro n hn
  absurd hn
  exact Nat.not_lt_zero n
  --end base case
  intro n2 hn2
  obtain l := sih n2
  obtain x : ∀ n < n2, P n := by
    intro y hy
    apply hk y
    rw [Nat.lt_succ_iff_lt_or_eq] at hn2
    rcases hn2 with hP | hQ
    exact Nat.lt_trans hy hP
    rw [hQ] at hy
    exact hy
  apply l
  exact x



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



--WOP → Induction. This isn't super easy, surely there's a way to simplify?
example (P: Nat → Prop) : (P 0 ∧ ∀ n, P n → P (n+1)) → ∀ n, P n := by
  intro ⟨bc, ih⟩
  set S := {n | ¬ (P n)}
  by_contra h
  push_neg at h
  obtain ⟨n,hn⟩ := h
  obtain hninS : n ∈ S := by exact hn
  obtain hS: S.Nonempty := by use n
  obtain ⟨aWOP,⟨aWOPS,haWOP⟩⟩ := WOP S hS
  obtain aWOPpos : aWOP ≠ 0 := by
    by_contra k
    rw [k] at aWOPS
    apply aWOPS
    exact bc
  --Next step involves applying the induction hypothesis to aWOP-1 to get a contradiction. This certainly would need to be simplified somehow to be a level
  absurd aWOPS
  obtain ihAWOP := ih (aWOP-1)
  rw [Nat.sub_one_add_one aWOPpos] at ihAWOP
  apply ihAWOP
  by_contra h
  obtain aWOPm1s : (aWOP-1) ∈ S := by exact h
  obtain contra : aWOP ≤ (aWOP-1) := by exact haWOP (aWOP-1) aWOPm1s
  rw [← Nat.pred_eq_sub_one,Nat.le_pred_iff_lt, lt_self_iff_false] at contra
  exact contra
  --Last step asks for a proof that aWOP is bigger than zero (so that all the aWOP-1 stuff is valid)
  rw [← Nat.pos_iff_ne_zero] at aWOPpos
  exact aWOPpos

--Structural induction?

--Another ex: A subset of ℤ+, 5 ∈ A, ∀m,n ∈ A m+n ∈ A, prove A = {5k ∣ k ∈ ℤ+}

--"Let F be the subset of ℕ such that 12 ∈ F and, if x ∈ F, x^2 ∈ F and 3x+8 ∈ F. Prove that every x ∈ F is divisible by 4."
inductive F : ℕ → Prop
  | base : F 12
  | h1   : ∀ x, F x → F (x ^ 2)
  | h2  : ∀ x, F x → F (3 * x + 8)

example : ∀ x, F x → (4 ∣ x) := by
  intro x hx
  induction' hx with k hk
  use 3
  obtain ⟨l,hl⟩ := a_ih
  rw [hl]
  use 4*l^2
  simplify
  obtain ⟨l,hl⟩ := a_ih
  rw [hl]
  use 3*l+2
  simplify

--Full binary trees
inductive FBT : Type
  | root : FBT
  | branch : FBT → FBT → FBT --Takes the left & right subtrees and glues them together into new FBT

def FBT.num_nodes : FBT → ℕ
  | .root => 1
  | .branch l r => l.num_nodes + r.num_nodes + 1

def FBT.num_edges : FBT → ℕ
  | .root => 0
  | .branch l r => l.num_edges + r.num_edges + 2

--If T is a full binary tree, its number of nodes is one more than its number of edges
example (T : FBT) : T.num_edges + 1 = T.num_nodes := by
  induction' T with b1 b2 hb1 hb2
  rw [FBT.num_edges, FBT.num_nodes] --closes automatically
  rw [FBT.num_edges, FBT.num_nodes,← hb1, ← hb2]
  simplify



/-

--Pigeonhole principle. Using Finset Nat (instead of Finset u for u : Type*) because Finset induction needs the underlying type to have "decidable equality"; you need to be able to check whether or not elements are equal so that inserting an element into a set can be checked to make sense or not
example (S T : Finset Nat) (f : Rel S T) (hf: isFunction f) (hst: #S > #T) : ¬ isInjective f := by
  induction' S using Finset.induction_on with k hk
  apply Nat.not_lt_zero at hst
  exfalso
  exact hst
  sorry


--Partial order on a finite set has a maximal element. Again, just using Nat to avoid decidable equality issues
example {u : Type*} (hu : Fintype u) (hne : Nonempty u) (R: Rel_on u) (hR: isPartialOrder R) : ∃ m, isMaximal R m := by
  induction' (Fintype.card u) with k hk
  sorry
  sorry
/-example (S : Fintype Nat) (hS: Fintype.Nonempty S) (R : Rel_on S) (hR: isPartialOrder R) : ∃ m, isMaximal R m  := by
  induction' S using Finset.induction_on with newelem newS
  exfalso
  rw [Finset.nonempty_iff_ne_empty] at hS
  apply hS
  rfl
  by_cases h : isMaximal R newelem
  sorry-/
-/
