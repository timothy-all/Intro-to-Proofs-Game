import Game.Levels.PfWorld.L04_pf

World "PfWorld"
Level 5

Title "Proofs of Conjunctions"

Introduction "
# **Level 5 : Proving Conjunctions**
The conclusion of the if-then statement of this proof is a conjunction. How do we handle this in Lean? The proof-strategy we implement is validated by the following logical equivalence
```
(P → (Q ∧ R)) ↔ (P → Q) ∧ (P → R)
```
In other words, to prove a conjunction we need only prove the individual parts of the conjunction separately.
>
But first, let's `intro` a generic integer and the hypothesis that $21$ is a divisor of that integer.
### **💡 Pro-tip**
Lean knows that the statement `21 ∣ n` is actually an existential statement, namely
```
21 ∣ n = ∃ k, n = 21 * k
```
Conveniently, we can destructure this statement within `intro`. 👉 Try
```
intro n ⟨k,hk⟩
```
"

/-- For all integers $n$, if $21$ divides $n$, then $7$ divides $n$ and $3$ divides $n$.-/
Statement : ∀ n : ℤ, 21 ∣ n → ( 7 ∣ n ∧ 3 ∣ n) := by
  intro n ⟨k,hk⟩
  Hint "Notice that `n k` are **Objects** and we have the assumption `hk : n = 21 * k`. The line
  ```
  intro n ⟨n,hk⟩
  ```
  is essentially short-hand for
  ```
  intro n h
  obtain ⟨n,hk⟩ := h
  ```
  Now, our goal is `⊢ 7 ∣ n ∧ 3 ∣ n`. We can split our work into two goals with the help of ...
  ### **❯ The `constructor` tactic**
  The `constructor` tactic will take a goal like `⊢ Q ∧ R` and split it into subgoals. The first subgoal is `⊢ Q` (under the same hypotheses as before) and the second subgoal is `⊢ R` (again, under the same hypotheses as before). 👉 Try it out with
  ```
  constructor
  ```"
  constructor
  Hint "We now have an *Active Goal* and a *Goal 2*. We can tab over to *Goal 2* if we like, but might as well address them in order. To prove `⊢ 7 ∣ n`, we need to profer a witness to the underlying existential statement `∃ d, n = 7 * d`. Can you find such a witness?"
  exist 3 * k
  Hint "***Perfect.*** Let's rewrite the left-hand side of our goal with `hk`."
  rw[hk]
  Hint "If only there were a tactic that could help us `simplify` basic arithmetic like in our current goal..."
  simplify
  Hint "***You got it.*** See if you can't finish from here."
  exist 7 * k
  rw[hk]
  simplify

Conclusion "### **💡 Pro-tip**
The `constructor` tactic is definitely handy but don't overuse it. For example, if you have two hypotheses, say `hP : P` and `hQ : Q`, and your goal is `⊢ P ∧ Q`, then the `constructor` tactic is overkill. Simply use
```
exact And.intro hP hQ
```
"

NewTactic constructor
