import Game.Levels.PfWorld.L03_pf

World "PfWorld"
Level 4

Title "Proof by Contradiction"

Introduction "
# **Level 4 : Proof by Contradiction**
Another method of indirect proof is **Proof by Contradiction**. The strategy is justified via the following logical equivalence
```
(¬ P → False) ↔ P
```
proven in Level 5 of Equivalence World.
>
First and foremost, our goal is a subset relation. So let's introduce the appropriate stuff with
```
intro a ha
```
"

/-- Suppose $A,B$ are sets such that their intersection is empty. Then $A ⊆ A \setminus B$.-/
Statement {u : Type*} (A B : Set u) (h : A ∩ B = ∅): A ⊆ A \ B := by
  intro a ha
  Hint "Our goal is now `⊢ a ∈ A \\ B`. Let's try to implement the proof-by-contradiction strategy. We can do this with the help of ...
  ### **❯ The `by_contra` tactic**
  The `by_contra` tactic implements the proof-by-contradiction strategy. Specifically, if the goal is `⊢ P`, then `by_contra F` (we can replace `F` with whatever identifier we wish) will change the goal to `⊢ False` and automatically introduce the hypothesis `F : ¬ P`. 👉 Try it out with
  ```
  by_contra F
  ```
  "
  by_contra F
  Hint "Now our goal is `⊢ False` and `F : a ∉ A \\ B`. Using what we know from Set World and Logical Equivalence World, let's rewrite `F` in the form:
  ```
  F : a ∈ A → a ∈ B
  ```
  "
  rw[mem_diff_iff,Not_and,Not_not,← Imp_iff_not_or] at F
  Hint "Great. We're aiming to show that `a ∈ A ∩ B` -- but this is `False` since we know `h : A ∩ B = ∅`. To get there, let's `obtain` the fact that `a ∈ B`."
  obtain hb := F ha
  Hint "Super. Now let's `obtain` the fact that `a ∈ A ∧ a ∈ B`."
  obtain hAB := And.intro ha hb
  Hint "Terrific. Now, let's rewrite `{hAB}` to say
  ```
  {hAB} : a ∈ A ∩ B
  ```
  "
  rw[← Set.mem_inter_iff] at hAB
  Hint "Amazing. Now let's rewrite `A ∩ B` in `{hAB}` as `∅`."
  rw[h] at hAB
  Hint "We can clear the goal in two different ways. Our goal is `⊢ False`; this is `exact`ly what is being said in `{hAB}`. Alternatively, we could use ...
  ### **❯ The `contradiction` tactic**
  One of our hypotheses definitionally says `False` (namely `{hAB}`). Whenever we have ahypothesis that is explicitly `False`, or we have a pair of hypotheses that are trivially contradictory (like suppose we have `h : P` and `h' : ¬ P` -- these hypotheses are contradictory) the the `contradiction` tactic will clear the goal. The idea being that under `False` assumptions, anything follows (remember: `False → True` is a `True` implication). Give it a try with
  ```
  contradiction
  ```
  "
  contradiction


Conclusion "### **💡 Pro-tip**
The `contradiction` tactic is most useful when discharging cases that are trivially contradictory.
"

NewTactic by_contra contradiction
