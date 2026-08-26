import Game.Levels.PfWorld.L06_pf

World "PfWorld"
Level 7

Title "Contradictory Interlude"

Introduction "
# **Level 7: Interlude**
There's nothing super new in this level, but it gives us an opportunity to point out some idiosyncracies about Lean.
>
First and foremost, we have an `↔` statement to prove. 👉 So let's get going with
```
constructor
```
"

Statement {u : Type*} (A : Set u) : A = ∅ ↔ ∀ {x}, x ∉ A := by
  constructor
  Hint "There's a few different paths we could take here. But let's take the opportunity to introduce ...
  ### **❯ The `by_contra!` tactic**
  The `by_contra!` tactic is identical to the `by_contra` tactic except it tries to push negations through the introduced hypothesis automatically. 👉 Give it a try here with:
  ```
  by_contra! F
  ```
  "
  by_contra! F
  Hint "Notice that our goal is `⊢ False` while the hypothesis `{F} : A = ∅ ∧ ∃ x, x ∈ A` -- this is the simplified negation of `A = ∅ → ∀ x, x ∉ A`. Let's obtain a witness to the right-hand side of the conjunction in `{F}`."
  obtain ⟨x,hx⟩ := F.right
  Hint "Great. Now let's rewrite the hypothesis `{hx} : x ∈ A` using `{F}.left`."
  rw[F.left] at hx
  Hint "We've got a couple options to clear the goal now."
  exact hx
  Hint "Great. Now we need to prove the **backward** direction of our bicondtional. Let's attack this somewhat directly. 👉 Let's start with
  ```
  intro h
  ```
  "
  intro h
  Hint "We now have a set-equality to prove. Let's rewrite this using `set_eq_iff`."
  rw[set_eq_iff]
  Hint "OK. Now, let's take care of the universal quantifier and `intro` a generic variable."
  intro x
  Hint "We've come to yet another biconditional! Let's use `constructor` to split our goals."
  constructor
  Hint "Great. Let's `intro` the hypothesis of the **forward** direction."
  intro hx
  Hint "Our goal is definitionally `⊢ False` (this is what `x ∈ ∅` truly means). We have `{h} : ∀ \{x : u}, x ∉ A`. Lean has a funny way of interpreting not-statements. In particular, Lean considers the following to be definitionally equaly:
  ```
  (¬ P) = (P → False)
  ```
  This means that if `nP : ¬ P` and `hP : P`, then `nP hP` is a proof of `False`. 👉 Let's try this here with
  ```
  exact h hx
  ```
  "
  exact h hx
  Hint "Goal cleared! See if you can't clear this last goal on your own."
  intro F
  contradiction


Conclusion ""

NewTactic by_contra!
DisabledTactic contrapose! --yay
