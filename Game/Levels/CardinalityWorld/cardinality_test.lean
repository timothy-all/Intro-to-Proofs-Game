import Game.Levels.InductionWorld.induction_test

/-Lines below set up sigma notation-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith

open Finset
open BigOperators


World "CardinalityWorld"
Level 1

Title "Cardinality test"

Introduction "."

--Placeholder level
Statement (n : Nat) : true := by
  rfl

Conclusion " "

/-
Main cardinality world goals:
- Equinumerous is an equivalence relation
- ℝ and ℕ are not equinumerous
- ℚ is countable (difficult?)

**HTPIL makes this way easier using usual functions. Maybe it could be worth it to abandon relation-functions here, or maybe start by showing how they fit in with Lean functions?
-/

--Basic cardinality setup and examples

def Equinumerous (u v : Type) := ∃ f : Rel u v, isFunction f ∧ isBijection f
infix:70 " ~ " => Equinumerous


theorem Nat_eqin_PNat : Nat ~ PNat := by
  let fnp : Rel Nat PNat := fun a b => a + 1 = b --Is "let" valid in the game?
  use fnp
  constructor
  intro a
  use! ⟨a+1, Nat.succ_pos a⟩ --Need to prove that a + 1 has type PNat to use it
  constructor
  rfl
  intro y h
  unfold fnp at h
  --rw [h]
  sorry
  --Bijective proof below has way too many small Nat/PNat manipulations, coercions
  constructor
  intro a1 a2 b ha1b ha2b
  rw [←Nat.succ_inj, Nat.succ_eq_add_one, Nat.succ_eq_add_one, ha1b, ha2b]
  intro b
  use (PNat.natPred b)
  --rw [fnp, PNat.natPred, Nat.sub_one_add_one] The rw worked moving fnp into the theorem
  --exact PNat.ne_zero b
  sorry



--Type and powerset of type not equinumerous

example (u : Type) : ¬ (u ~ Set u) := by
  rw [Equinumerous]
  push_neg
  intro f hf
  rw [isBijection, Not_and]
  right
  rw [isSurjective]
  push_neg --Have to construct the problem set; uses function outputs so it's automatically awkward. The uniqueness is needed to prove the theorem & I'm not sure how to utilize it
  let elem_not_in_output (a : u) : Prop := by
    obtain hfa := Classical.choose (hf a) --Probably no way around Classical.choose since you have to grab an output
    exact (a ∉ hfa) --I don't think the proof works without using the uniqueness somehow
  let S : Set u := { a : u | elem_not_in_output a }
  use S
  intro a
  by_cases h : a ∈ S --same as elem_not_in_output a
  by_contra
  obtain k : ¬ elem_not_in_output a := by

    sorry
  sorry
  sorry
