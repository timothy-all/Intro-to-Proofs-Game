import Game.Levels.PfWorld.L09_pf

World "PfWorld"
Level 10

Title "Antisymmetric biconditional"

Introduction "
# **Level 10: Antisymmetric biconditional**
Here's an example of a biconditional statement where the **forward** direction is quite straightforward whereas the **backward** direction is quite tricky! Use `constructor` to split your goals and clear the first goal on your own.
"

open Set

/-- Let $n$ be an integer. Then $40$ divides $n$ if and only if if $8$ divides $n$ and $5$ divides $n$.-/
Statement (n : ℤ) : 40 ∣ n ↔ (8 ∣ n ∧ 5 ∣ n) := by
  constructor
  intro ⟨k,hk⟩
  constructor
  exist  5 * k
  rw[hk]
  simplify
  exist  8 * k
  rw[hk]
  simplify
  Hint "***Excellent.*** Things are about to get harder. Let's introduce the right stuff. We can do this in one go with
  ```
  intro ⟨ ⟨k,hk⟩, ⟨j,hj⟩ ⟩
  ```
  The *outer* angled brackets tell Lean that your introducing components of a conjunction; the inner angled brackets destructure the existential statements that are being glued together by `∧`.
  "
  intro ⟨⟨k,hk⟩, ⟨j,hj⟩⟩
  Hint "***Perfect.*** We now need a clever idea. What's the first multiple of `5` that differs from a multiple of `8` by `1`? The answer: `15` and `16`.

  Now, let's obtain the fact that `15 * n = 120 * k`. We need to open a new subgoal to prove this. We can use the `obtain` tactic to do so with the following syntax. 👉 Try
  ```
  obtain h1 : 15 * n = 120 * k
  ```
  "
  obtain h1 : 15 * n = 120 * k
  Hint "***Amaze, amaze.*** Notice how our *Active Goal* is now `⊢ 15 * n = 120 * k` while *Goal 2* gets back to our original goal. See if you can't clear this subgoal on your own."
  rw[hk]
  simplify
  Hint "***Super.*** Now, using the same ideas, `obtain` the hypothesis `h2 : 16 * n = 80 * j`."
  obtain h2 : 16 * n = 80 * j
  rw[hj]
  simplify
  Hint "***Look at you go.*** Now, `obtain` one more hypothesis. Specifically, obtain the hypothesis that starts with `h3 : n = ...` -- the right-hand side of this equality ought to be a difference of multiples of `40`."
  obtain h3 : n = 80 * j - 120 * k
  rw[← h1,← h2]
  simplify
  Hint "We're finally ready to profer a witness to our existential goal. Try to finish this level off on your own from here."
  exist  2*j - 3*k
  rw[h3]
  simplify

Conclusion ""
