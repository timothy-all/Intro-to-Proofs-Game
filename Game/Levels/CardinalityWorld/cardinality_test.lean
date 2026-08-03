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

def Equinumerous (u v : Type) := ∃ f : u → v, f.Bijective
infix:70 " ~ " => Equinumerous

--Starting to think a subtype tutorial will be needed for this
--This problem feels awkward because the Nat/PNat stuff needed, but maybe it would be natural after a subtype tutorial?
theorem Nat_eqin_PNat : Nat ~ PNat := by
  let fnp : ℕ → PNat := fun a => ⟨a.succ, Nat.succ_pos a⟩ --Is "let" valid in the game? Definition has to be passed a proof that a is positive. Kind of awkward, but makes sense & should probably just be a natural part of cardinality world
  use fnp
  constructor
  intro a b ha
  apply (Nat.succ_inj).mp
  unfold fnp at ha
  injection ha with h --The injection tactic uses that "subtype constructors are injective" to extract the succ equality
  intro y
  use PNat.natPred y
  unfold fnp
  unfold PNat.natPred
  exact PNat.succPNat_natPred y



--Type and powerset of type not equinumerous. Not too bad
example (u : Type) : ¬ (u ~ Set u) := by
  rw [Equinumerous]
  push_neg
  intro f
  rw [Function.Bijective, and_iff_not_or_not, not_not]
  right
  rw [Function.Surjective]
  push_neg
  let S : Set u := { a : u | a ∉ f a }
  use S
  intro a
  by_cases k: a ∈ S
  apply Ne.symm (ne_of_mem_of_not_mem' k k) --Closes first case by itself. Maybe this lemma could be an earlier set level?
  intro h
  obtain l : a ∈ S := by
    rw [← h] at k
    exact k
  exact k l
