import Game.Metadata
import Mathlib.Tactic.Cases -- makes induction' accessible
import Game.Levels.InductionWorld.L01_Induction

/-Lines below set up sigma notation-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Finset
open BigOperators


World "InductionWorld"
Level 2

Title "Basic Induction"

Introduction "Let's try something a bit less trivial. We'll prove that the sum of the first `n+1` even natural numbers is `n(n+1)`.

Take a look at how Lean deals with sums written in sigma notation: `∑ k ∈ range (n+1), 2*k`. First, `range n` is shorthand for the set `{0,1,…,n-1}`, so `∑ k ∈ range (n+1), 2 * k` tells Lean to take the sum of twice the elements of `range (n+1)`. More concretely, we'd say this is the sum of `2k` as `k` ranges from `0` to `n`."

Statement (n : Nat) : ∑ k ∈ range (n+1), 2*k = n*(n+1) := by
  Hint "Let's proceed by induction on `n`: `induction n with k ih`."
  induction' n with k ih
  Hint "Let's talk about some Lean facts needed to manipulate sigma notation.

  First off, base cases often deal with `range 1` when starting with a `n = 0` case. We can `rw [range_one]` to simplify the `range` into the simpler set containing 1 (won't let me use curly braces ???).

  Then, Lean has a theorem specially for summing over one element sets: `rw [sum_singleton]`. Since the resulting goal follows from basic arithmetic, Lean automatically closes the goal (`simplify` would work even if it didn't)."
  rw [range_one,sum_singleton]
  Hint "In the inductive step, we have to relate the goal to the induction hypothesis, which Lean has named `a`. In written proofs, we would pull out the last term of the sum. Lean's theorem for this is `sum_range_succ` - rewrite using it."
  rw [sum_range_succ]
  Hint "Can you take it from here? Remember, `simplify` can help close algebraic goals, but it doesn't look at your hypotheses; maybe a rewrite will help first."
  rw [ih]
  simplify


Conclusion " "
