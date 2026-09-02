import GameServer


/--
The `contrapose` tacic turns a goal of the form `⊢ P → Q` into `⊢ ¬ Q → ¬ P`.
-/
TacticDoc contrapose

/--
The `contrapose!` tacic turns a goal of the form `⊢ P → Q` into `⊢ ¬ Q → ¬ P` and pushes negations through (with `push_neg`).
-/
TacticDoc contrapose!

/--
The `simplify` tactic will attempt to clear the goal by applying *very* basic simplification rules to the goal. For example, if the goal is to prove `⊢ x * (y + z) = x * y + x * z` then `simplify` will clear the goal.
-/
TacticDoc simplify

/--
This is the defintion of what it means to say that an integer is *even*. Here's what it looks like in Lean:
```
isEven (x : Int) := ∃ k, x = 2 * k
```
-/
DefinitionDoc isEven as "NT: isEven"

/--
This is the defintion of what it means to say that an integer is *odd*. Here's what it looks like in Lean:
```
isOdd (x : Int) := ∃ k, x = 2 * k + 1
```
-/
DefinitionDoc isOdd as "NT: isOdd"

/--
The tactic `by_contra` changes a goal of the form `⊢ P` to `⊢ False` and adds the hypothesis `this : ¬ P` to the proof-state. One can name the introduced hypothesis `this` with an optional identifier. For example, `by_contra F` changes the goal to `⊢ False` and adds the hypothesis `F : ¬ P`.
-/
TacticDoc by_contra

/--
The tactic `by_contra!` is the same as `by_contra` except that it applies `push_neg` automically to the introduced hypothesis.
-/
TacticDoc by_contra!

/--
The `contradiction` tactic closes the main goal if its hypotheses are "trivially contradictory". For example, if there are two hypotheses in the proof-state `h₁ : P` and `h₂ : ¬ P`, then `contradiction` will clear the goal.
-/
TacticDoc contradiction

/--
The `constructor` tactic is useful for splitting goals of the form `⊢ P ∧ Q`. In this case, `constructor` will split the main goal into two subgoals; the first goal will be `⊢ P` while the second will be `⊢ Q`.
-/
TacticDoc constructor


/--
The `refine` tactic acts like a combination of `constructor` and `exact`. For example, suppoes the goal is `⊢ P ∧ Q`, but there are hypotheses in the proof state like `h : R`, `h₁ : R → P`, and `h₂ : Q`. Then `refine ⟨h₁ h, h₂⟩` clears the goal.

The `refine` tactic also accepts wildcards. For example, if the goal is `⊢ P ∧ Q`, then `refine ⟨?_,?_⟩` is the same as `constructor`.
-/
TacticDoc refine

/--
The tactic `apply h` attemps to match the conclusion of `h` to the current goal. If it succeeds, then it opens subgoals according to the hypotheses of `h`. For example, suppose `h: P → Q` and the current goal is `⊢ Q`. Then `apply h` will change the goal to `⊢ P`.
-/
TacticDoc apply

/--
The `exist!` tactic is helpful for existence/uniqueness goals. Specifically, if the goal is of the form `∃! x, P x` and `a : u` is a witness to goal, then `exist! a` will split the goal into two subgoals. The first goal is `⊢ P a` (the existence statement). The second goal is `⊢ ∀ y, P y → y = 0` (the uniqueness statement).
-/
TacticDoc exist!

/--
The `by_cases` tactic will split the goal into two cases. Specifically, if `P` is a proposition (supplied by the player), then `by_cases h : P` will add the hypothesis `h : P` to the first case while adding the hypothesis `h : ¬ P` to the second case.
-/
TacticDoc by_cases

/--
If $A ⊆ B$ and $B ⊆ A$, then $A = B$.
-/
TheoremDoc Double_inclusion as "SET: Double_inclusion"


/-- If $A$ is not equal to the empty set, then there exists an element $x$ such that $x ∈ A$ (i.e., $A$ is nonempty).-/
TheoremDoc Ne_empty_iff_nonempty as "SET: Ne_empty_iff_nonempty"
