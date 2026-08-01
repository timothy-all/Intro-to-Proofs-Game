import Game.Levels.FunctionWorld.FunctionWorldExamples.function_example6

/-Lines below set up sigma notation-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith

open Finset
open BigOperators


World "LeanFunctionWorld"
Level 1

Title "."

Introduction "."

--Placeholder level
Statement (n : Nat) : true := by
  rfl

Conclusion " "

/-



-/

/-Using a Lean function, if you define a Rel in the obvious way, it's a function as previously defined. I wasn't able to include the function as a default argument & still do the proof, there was some kind of subtle optParam thing going on.

This could be the first level, including text explaining what the `fun` part is doing and the `f: u → v` notation
-/
example (u v : Type*) (f : u → v) : isFunction (fun a b => f a = b) := by
  intro a
  use! f a
  constructor
  rfl
  intro y hy
  rw [hy]


--Lean identity function
def Fun_id (u: Type*) : u → u := fun a => a

--Function composition level to show how that works

--Level that requires student





/-
The formula below definitely should be true, but defining `f` might be weird. You'd need to extract the output from isFunction so Classical.choice stuff might be needed?-/
example (u v : Type) (R : Rel u v) (hf: isFunction R) :   ∃ f : u → v, ∀ x : u, ∀y : v, f x = y ↔ R x y := by
  sorry



--A level should have them define a function to solve a problem because this will be used a million times in cardinality world
