import Game.Levels.RelationWorld
import Game.Levels.FunctionWorld.Metadata_FunctionWorld
import Game.Levels.FunctionWorld.Function_docs
import Mathlib.Tactic.Cases


World "FunctionWorld"
Level 1

Title "Functions 1"

Introduction "## **Level 1 : Definition of Function**

We'll view functions in Lean as relations with an additional special property, just as we did in class.

🔍 If `R : Rel u v`, `R` will be a function if `∀ a : u, ∃! b : v, R a b`. We'll call this property `isFunction R` - check your inventory for details.

Let's start very simple to get practice with this: we'll prove that the identity relation is a function."


/-- The identity relation is a function.-/
Statement Fun_identity_fun {u : Type*} : isFunction (Rel_id u) := by
  Hint "Let's unpack what it means to be a function. 👉 Start with `intro a` to grab an arbitrary element of `u`."
  intro a
  Hint "Since the identity relation is only supposed to have pairs `(a,a)`, let's claim that `a` is the unique `b` the goal is asking for: 👉 `exist! a`."
  exist! a
  Hint "By definition, `Rel_id u a a` means `a = a`. Cite the reflexive property of equality: 👉 `rfl`."
  rfl
  Hint "Can you finish from here?"
  intro y hy
  rw [Rel_id] at hy
  rw [hy]





Conclusion "Often, using `isFunction` directly is sort of a pain. The next level will discuss some ways to streamline it!"

NewDefinition isFunction
NewTheorem Fun_identity_fun
