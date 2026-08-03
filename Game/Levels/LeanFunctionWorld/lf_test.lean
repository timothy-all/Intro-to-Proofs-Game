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

This could be the first level, including text explaining what the `fun` part is doing and the `f: u → v` notation. Since this is a function of 2 variables, maybe it isn't a good first level and should maybe be at the end?
-/
example (u v : Type*) (f : u → v) : isFunction (fun a b => f a = b) := by
  intro a
  use! f a
  constructor
  rfl
  intro y hy
  rw [hy]


--Identity function we can use
def Fun_id (u: Type*) : u → u := fun a => a

/-Identity function is bijective. Commented below is what we need if we use the built-in identity function (the @ is required to pass u properly, otherwise it tries to plug u into id). By using Fun_id above, the @ isn't needed
example (u : Type) : Function.Bijective (@id u) := by-/
example (u:Type*) : Function.Bijective (Fun_id u) := by
  constructor
  intro x y h
  rw [Fun_id,Fun_id] at h
  exact h
  intro y
  use y
  rw [Fun_id]



--We'll need to set a definition of invertible since the one from the book uses relations. There's a built-in Lean theorem showing that this is equivalent to f being bijective, but I think this would be a great level
def Function.Invertible {u v : Type*} (f : u → v) : Prop := f.HasLeftInverse ∧ f.HasRightInverse

--Level for left inverse iff injective. I originally thought this might be a good level, leading up to proving invertible iff bijection, but there's a bunch of classical stuff that might be bad
--Unfortunately Classical.choice is required to grab an element of `u` using `Nonempty u`. Might be a way to get around this with `Inhabited u`?
--
example {u v : Type*} {f : u → v} {hu : Nonempty u} : f.HasLeftInverse ↔ f.Injective := by
  classical --This is required for the second part. There's no way around this because of having to define the left inverse, which requires picking preimages... Might there be a way to use `classical` automatically for the whole game?
  constructor
  intro h x y hxy
  obtain ⟨g,hg⟩ := h
  obtain gfx : g (f x) = x := by apply hg
  obtain gfy : g (f y) = y := by apply hg
  rw [hxy] at gfx
  rw [← gfx,gfy]

  --The second case requires defining a piecewise function (and this specific one needs Classical stuff). Cardinality part likely will need some piecewise stuff
  obtain elem : u := Classical.choice hu
  let inv : v → u := fun x => if h : ∃ y, f y = x then Classical.choose h else elem
  intro hi
  use inv
  intro x
  unfold inv
  split_ifs with k --This line doesn't work without unfold on the previous line
  exact hi (Classical.choose_spec k) --This massively confuses me, I had to ask AI how to close the goal
  push_neg at k
  exfalso
  exact k x rfl --I also got this line from AI...





/-Level to show f(x) = x + 3 from ℤ to ℤ is invertible to work with composites & making them define a function.
 -/
def Fun_ex1 : ℤ → ℤ := fun x => x+3
def Function.Inverse {u v : Type*} (f: u → v) : v → u

example : Function.HasRightInverse Fun_ex1 := by
  --Provide the right inverse
  use (fun x => x - 3)
  --Prove it's the right inverse
  intro x
  rw [Fun_ex1]
  --I think (fun x => x-3) x is definitionally x-3, so this is asking for a proof that (x-3)+3 = x. So ring works
  ring

example : Function.HasLeftInverse Fun_ex1 := by
  use (fun x => x - 3)
  intro x
  rw [Fun_ex1]
  ring




/-
The formula below definitely should be true, but defining `f` might be weird. You'd need to extract the output from isFunction so Classical.choice stuff might be needed?
-/
example (u v : Type) (R : Rel u v) (hf: isFunction R) :   ∃ f : u → v, ∀ x : u, ∀y : v, f x = y ↔ R x y := by
  sorry
