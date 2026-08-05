import Game.Levels.InductionWorld.induction_test
import Game.Levels.LeanFunctionWorld.lf_test

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

def Equinumerous (u v : Type*) := ∃ f : u → v, f.Bijective
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
  injection ha with h --The injection tactic uses that "subtype constructors are injective" to extract the succ equality. Alternatively, grind closes this.
  intro y
  use PNat.natPred y --Grind can't be used to simplify this one, seemingly. Using the more obvious y-1 doesn't help either
  unfold fnp
  unfold PNat.natPred
  exact PNat.succPNat_natPred y

--Equinumerous is an equivalence relation. Uses a few lemmas that could be in Lean Function World

theorem Equinumerous.refl (u : Type*) : u ~ u := by
  use LF_id u
  exact LF_id_bij u

theorem Equinumerous.symm (u v : Type*) : u ~ v → v ~ u := by
  intro h
  obtain ⟨f,hf⟩ := h
  use LF_inv_of_bij f hf
  exact LF_inv_of_bij_bij f hf

theorem Equinumerous.trans (u v w : Type*) : u ~ v → v ~ w → u ~ w := by
  intro huv hvw
  obtain ⟨fuv, hfuv⟩ := huv
  obtain ⟨fvw, hfvw⟩ := hvw
  use fvw ∘ fuv
  refine ⟨LF_comp_inj_of_inj fuv fvw hfuv.left hfvw.left, LF_comp_surj_of_surj fuv fvw hfuv.right hfvw.right⟩

theorem Card_cartprod_equinumerous {a b c d : Type*} (hab : a ~ b) (hcd : c ~ d) : (a × c) ~ (b × d) := by
  obtain ⟨fab, hfab⟩ := hab
  obtain ⟨fcd, hfcd⟩ := hcd
  use fun (x : (a × c))  ↦ ((fab x.1, fcd x.2) : (b × d)) --If you use, for instance, the more natural `(x1,x2) : (a × c)` for the input, the function definition gets bogged down with a `match` definition
  constructor
  intro (x1,x2) (y1,y2) hxy
  rw [Prod.mk_inj] at hxy
  obtain ⟨fabx1y1,fcdx2y2⟩ := hxy
  rw [Prod.mk_inj]
  refine ⟨hfab.left fabx1y1, hfcd.left fcdx2y2⟩ --Ends injective part

  intro (y1,y2)
  obtain ⟨x1,hx1⟩ := hfab.right y1
  obtain ⟨x2,hx2⟩ := hfcd.right y2
  use (x1,x2)
  rw [Prod.mk_inj]
  refine ⟨hx1,hx2⟩




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
  apply Ne.symm (ne_of_mem_of_not_mem' k k) --Closes first case by itself. Maybe this lemma (the ne_of_mem_of_not_mem') could be an earlier set level? Alternatively, grind closes this. But placing grind on the next line finishes the rest of the proof immediately, which might be ok?
  intro h
  obtain l : a ∈ S := by
    rw [← h] at k
    exact k
  exact k l
