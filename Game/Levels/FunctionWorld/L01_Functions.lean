import Game.Metadata
import Game.Levels.RelationWorld.RelationWorldExamples
import Mathlib.Tactic.Cases


World "FunctionWorld"
Level 1

Title "f"

Introduction "We'll view functions in Lean as relations with an additional special property, just as we did in class.

If `R : Rel u v`, `R` will be a function if `∀ a : u, ∃! b : v, R a b`. We'll call this property `isFunction R`.

Let's start very simple to get practice with this: we'll prove that the identity relation is a function."



Statement (n : Nat) : 2*n = n+n := by
  Hint "To get Lean to begin a proof by induction on `n`, we'll write `induction' n with h ih`. What does this mean?

  - `induction' n` tells Lean to induct on `n`. The prime following `induction` lets use the version that names hypotheses.
  - The `with k ih` part names the variables showing up in the induction proof. The arbitrary variable in the induction step will be `k`, and the induction hypothesis will be `ih`."
  induction' n with k ih
  Hint "We're now automatically asked to prove the base case for induction, which is the case when `n = 0`.

  To close this goal, let's use the `simplify` tactic. This tactic will close all goals that follow from basic algebraic operations."
  simplify
  Hint "Now we're automatically moved to the inductive step. This also requires simple algebraic manipulation to solve; `simplify` to complete the proof."
  simplify




Conclusion "In fact, using `simplify` right from the start will close this goal! Try it. This, of course, won't work on more complicated examples."


/-- If `R: Rel u v`, `isFunction R` means that `R` is a function from `u` to `v`; that is, for every `a : u`, there is a unique `b : v` such that `R a b`. --/
DefinitionDoc isFunction as "FUN: isFunction"
