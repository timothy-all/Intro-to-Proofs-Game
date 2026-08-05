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

/- Function stuff to have examples of/add to the inventory at some point

- Investigate using ↦ in function definitions, might be nice & natural
- Using Bijective as a hypothesis ends up with a lot of .left and .right
- Function.Injective/Surjective/Bijective
- LF_id (Lean function identity function)
- LF_inv_of_bij (Grabs the inverse of a bijective function. You can do this a lot more carefully with left/right inverses but you run into the issue of needing types to be nonempty so you can grab elements.)
- LF_inv_of_bij_bij (Proof that the inverse is a bijection; unfinished.)
- There's some cartesian product stuff in cardinalityworld; Prod.mk_inj is useful for reducing equality to components. This currently isn't discussed in the cartesian product part of relationworld because that part is done using cartesian products of sets. Grind also solves a lot of the goals involving component manipulation




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
def LF_id (u: Type*) : u → u := fun a => a

/-Identity function is bijective. Commented below is what we need if we use the built-in identity function (the @ is required to pass u properly, otherwise it tries to plug u into id). By using Fun_id above, the @ isn't needed
example (u : Type) : Function.Bijective (@id u) := by-/
theorem LF_id_bij (u:Type*) : Function.Bijective (LF_id u) := by
  constructor
  intro x y h
  rw [LF_id,LF_id] at h
  exact h
  intro y
  use y
  rw [LF_id]



noncomputable def LF_inv_of_bij {u v : Type*} (f : u → v) (hf : f.Bijective) : v → u := fun y : v ↦ Classical.choose (hf.right y)

theorem LF_inv_of_bij_bij {u v : Type*} (f : u → v) (hf: f.Bijective) : (LF_inv_of_bij f hf).Bijective := by
  --Proof strategy will be to show the supposed inverse has f as a left inverse and a right inverse, then it follows from Function.bijective_iff_has_inverse
  obtain hleft : f.LeftInverse (LF_inv_of_bij f hf) := by --Surjective direction
    intro y
    exact Classical.choose_spec (hf.right y) --This makes me kind of uncomfortable. Currently not completely okay with Classical.choose/choose_spec
  obtain hright : f.RightInverse (LF_inv_of_bij f hf) := by --Injective direction
    intro x
    --obtain preim := Classical.choose (hf.right (f x))
    --obtain hp : preim = x := by
    --  apply hf.left
    unfold LF_inv_of_bij
    sorry
    --Not sure how to finish
  obtain final : ∃ g, Function.LeftInverse g (LF_inv_of_bij f hf) ∧ Function.RightInverse g (LF_inv_of_bij f hf) := by use f
  exact Function.bijective_iff_has_inverse.mpr final --Surely this & the previous line can be combined into one line, but I couldn't figure out how to do the `use`


theorem LF_comp_surj_of_surj {u v w : Type*} (f : u → v) (g: v → w) (hf: f.Surjective) (hg: g.Surjective) : (g ∘ f).Surjective := by
  intro z
  obtain ⟨y,hy⟩ := hg z
  obtain ⟨x,hx⟩ := hf y
  use x
  rw [Function.comp, hx, hy] --Doesn't work without the Function.comp call

theorem LF_comp_inj_of_inj {u v w : Type*} (f : u → v) (g: v → w) (hf: f.Injective) (hg: g.Injective) : (g ∘ f).Injective := by
  intro x y hxy
  apply hf
  apply hg
  exact hxy --Why doesn't this need a Function.comp call first? Is exact doing it automatically?







---------------------------------- Pre 8/5

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
  apply k x
  rfl





/-Level to show f(x) = x + 3 from ℤ to ℤ is invertible to work with composites & making them define a function.
 -/
def Fun_ex1 : ℤ → ℤ := fun x => x+3

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
