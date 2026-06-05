import Game.Metadata
import Game.Levels.RelationWorld.RelationWorldExamples
import Mathlib.Tactic.Cases


World "FunctionWorld"
Level 1

Title "f"

Introduction "We'll view functions in Lean as relations with an additional special property, just as we did in class.

If `R : Rel u v`, `R` will be a function if `∀ a : u, ∃! b : v, R a b`. We'll call this property `isFunction R`.

Let's start very simple to get practice with this: we'll prove that the identity relation is a function."

/--  The identity relation `Rel_id u` on set `u` is a function. -/
TheoremDoc Fun_identity_fun as "FUN: Fun_identity_fun"

Statement Fun_identity_fun {u : Type*} : isFunction (Rel_id u) := by
  Hint "Let's unpack what it means to be a function. Start with `intro a` to grab an arbitrary element of `u`."
  intro a
  Hint "Since the identity relation is only supposed to have pairs `(a,a)`, let's claim that `a` is the unique `b` the goal is asking for: `use! a`."
  use! a
  Hint "Use `constructor` to break apart our new `and` goal."
  constructor
  Hint "By definition, `Rel_id u a a` means `a = a`. Cite the reflexive property of equality for why this is true using `rfl`."
  rfl
  Hint "Can you finish from here?"
  intro y hy
  rw [Rel_id] at hy
  exact hy.symm





Conclusion "."


/-- If `R: Rel u v`, `isFunction R` means that `R` is a function from `u` to `v`; that is, for every `a : u`, there is a unique `b : v` such that `R a b`. --/
DefinitionDoc isFunction as "FUN: isFunction"
