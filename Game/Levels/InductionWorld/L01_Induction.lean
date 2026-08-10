import Game.Metadata
import Game.Levels.FunctionWorld.FunctionWorldExamples
import Mathlib.Tactic.Cases


World "InductionWorld"
Level 1

Title "Basic Induction"

Introduction "In Lean, we can prove theorems using induction for any statement using an ''inductive data type.'' The main inductive data type that we'll use is `Nat`, the type of natural numbers.

Let's start with a very easy example to see how we can use induction in Lean. We'll prove that multiplying a natural number by `2` is the same thing as adding it to itself."



Statement (n : Nat) : 2*n = n+n := by
  Hint "To get Lean to begin a proof by induction on `n`, we'll write `induction' n with h ih`. What does this mean?

  - `induction' n` tells Lean to induct on `n`. The prime following `induction` lets use the version that names hypotheses.
  - The `with k ih` part names the variables showing up in the induction proof. The arbitrary variable in the induction step will be `k`, and the induction hypothesis will be `ih`."
  induction' n with k ih
  Hint "We're now automatically asked to prove the base case for induction, which is the case when `n = 0`.

  To close this goal, let's use the `simplify` tactic. This tactic will close all goals that follow from basic algebraic operations."
  rfl --This level has to be reworked; adding push_cast to simplify made simplify close the whole goal because, for some reason, push_cast closes the base case
  Hint "Now we're automatically moved to the inductive step. This also requires simple algebraic manipulation to solve; `simplify` to complete the proof."
  simplify




Conclusion "In fact, using `simplify` right from the start will close this goal! Try it. This, of course, won't work on more complicated examples."
