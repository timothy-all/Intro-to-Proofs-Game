import GameServer


/--
The `contrapose` tacic turns a goal of the form `⊢ P → Q` into `⊢ ¬ Q → ¬ P`.
-/
TacticDoc contrapose

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
DefinitionDoc isEven as "isEven"

/--
The tactic `by_contra` changes a goal of the form `⊢ P` to `⊢ False` and adds the hypothesis `this : ¬ P` to the proof-state. One can name the introduced hypothesis `this` with an optional identifier. For example, `by_contra F` changes the goal to `⊢ False` and adds the hypothesis `F : ¬ P`.
-/
TacticDoc by_contra

/--
The `contradiction` tactic closes the main goal if its hypotheses are "trivially contradictory". For example, if there are two hypotheses in the proof-state `h₁ : P` and `h₂ : ¬ P`, then `contradiction` will clear the goal.
-/
TacticDoc contradiction
