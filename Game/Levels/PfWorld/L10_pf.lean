import Game.Levels.PfWorld.L09_pf

World "PfWorld"
Level 10

Title "Disjunctive hypotheses"

Introduction "
# **Level 10: Disjunctive hypotheses**
How do we use an `∨` hypothesis in a proof? We use cases! The following logical equivalence justifies our approach:
$$
\\begin{aligned}
  (P ∨ Q) → R &↔ ¬ (P ∨ Q) ∨ R \\\\
  &↔ (¬ P ∧ ¬ Q) ∨ R \\\\
  &↔ (¬ P ∨ R) ∧ (¬ Q ∨ R) \\\\
  &↔ (P → R) ∧ (Q → R)
\\end{aligned}
$$
In other words, if we have a hypothesis like `h : P ∨ Q`. Then we should split our goal into two: one in which we assume `P` and the other in which we assume `Q`. Let's see how this works in Lean.
>
Our initial goal is a subset relation. So let's `intro` the appropriate material to reckon with the unversal quantifier and if-then statement underneath the `⊆` relation.
"

--Or statement

/-- Suppose $A,B,C$ are sets and that $A ∪ C = B ∪ C$. Then the symmetric difference $(A \setminus B) ∪ (B \setminus A)$ is contained in $C$. -/
Statement {u : Type*} (A B C : Set u) (h : A ∪ C = B ∪ C) : (A \ B ∪ B \ A) ⊆ C := by
  intro x hx
  Hint "***Fantastic.*** Look at our introduced hypothesis `{hx}`. This is an `∨` statement. How to `obtain` the two cases `{x} ∈ A \\ B` and `{x} ∈ B \\ A`? We use the `obtain` tactic! 👉 Specifically, try
  ```
  obtain hxa | hxb := {hx}
  ```
  The **vertical bar** tells Lean that `{hx}` is an `∨`-statement and that we wish to split our goal into two; the first in which we obtain the hypothesis `hxa : x ∈ A \\ B` and the second in which we obtain the hypothesis `hxb : x ∈ B \\ A`.
  "
  obtain hxa | hxb := hx -- here
  Hint "Notice our assumption `{hxa} : {x} ∈ A \\ B` is now in our proof-state, what's more, we have two goals. Let's make a third goal! Given `h` it seems like it would be good to obtain `{x} ∈ A ∪ C`. 👉 So let's try
  ```
  obtain hxAC : {x} ∈ A ∪ C
  ```
  "
  obtain hxAC : x ∈ A ∪ C
  Hint "Now we have three goals! Our *Active Goal* is to prove `⊢ {x} ∈ A ∪ C`. See if you can't clear this on your own."
  left
  exact hxa.left
  Hint "Let's use `h` to rewrite `{hxAC}` to say that `x ∈ A ∪ B`."
  rw[h] at hxAC
  Hint "We have another `∨` hypothesis, namely `{hxAC} : {x} ∈ B ∪ C`. Use `obtain` to split our proof into cases."
  obtain hxB | hxC := hxAC
  Hint "This case seems contradictory... you need to a little work before you can use the `contradiction` tactic to clear it though."
  obtain hxB' := hxa.right
  contradiction
  Hint "***Great.*** The goal in this case is `exact`ly one of our hypotheses."
  exact hxC
  Hint "We're now in the original *second* case, that being, we're now assuming `{hxb} : x ∈ B \\ A`. See if you can't clear this on your own now that we've walked through the first case together."
  obtain hxBC : x ∈ B ∪ C
  left
  exact hxb.left
  rw[← h] at hxBC
  obtain hxA | hxC := hxBC
  obtain hxA' := hxb.right
  contradiction
  exact hxC


Conclusion ""
