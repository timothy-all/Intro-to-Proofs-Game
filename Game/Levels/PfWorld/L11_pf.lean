import Game.Levels.PfWorld.L10_pf

World "PfWorld"
Level 11

Title "Disjunctive Goals"

Introduction "
# **Level 11: Disjunctive Goals**
Suppose we have a goal like `⊢ P ∨ Q`. Sometimes we prove this directly by proving either `P` or `Q`. Other times, this doesn't work so well. What are some other strategies?
>
Here's an idea: break down into two cases; the first case assumes that `P` is true (so that our goal is easily met); the second case assumes that `¬ P` is true (so that our goal really comes to prove `Q`). But how do we *introduce* our own cases in Lean? We use ...
### **❯ The `by_cases` tactic**
The `by_cases` tactic helps to introduce custom cases. Specifically, `by_cases h : Prop` where `Prop` is some proposition will split the goal into two subgoals. In the first subgoal, we'll have the assumption `h : Prop`; in the second subgoal, we'll have the assumption `h : ¬ Prop`. 👉 In our case, try:
```
by_cases hAB : A ⊆ B
```
"

open Set

/-- Suppose the powerset of $A ∪ B$ is equal to the union of the powersets for $A$ and $B$ individually. Then it must be that either $A ⊆ B$ or $B ⊆ A$.-/
Statement  {u : Type*} (A B : Set u) (h : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : (A ⊆ B ∨ B ⊆ A) := by
  by_cases hAB : A ⊆ B
  Hint "***Great,*** we're in two cases. The `left`-hand side of our goal is `exact`ly one of our hypotheses. Clear this."
  left
  exact hAB
  Hint "***Excellent.*** Let's focus on proving the `right`-hand side of our goal now (since we know that `{hAB} : ¬ A ⊆ B`)."
  right
  Hint "***Super.*** Let's clean up our hypotheses before tackling this goal. First, let's rewrite `{hAB}` using `subset_iff` and `Not_forall`."
  rw[subset_iff,Not_forall] at hAB
  Hint "Now let's use `obtain` to grab a witness from the existential statement in `{hAB}`."
  obtain ⟨a,ha⟩ := hAB
  Hint "***OK.*** Now use logical equivalences to rewrite `{ha}` in the following form `{a} ∈ A ∧ {a} ∉ B`."
  rw[Imp_iff_not_or,Not_or,Not_not] at ha
  Hint "Our hypotheses look about as simple as we could hope. Let's address the goal and `intro` the right stuff."
  intro b hb
  Hint "Where to go from here? The main idea is to try to prove that `\{{a},{b}} ⊆ A` via the hypothesis `h`. As a first step, let's try to show `\{{a},{b}} ∈ 𝒫 (A ∪ B)`. Use `obtain` to open a new subgoal where this is the target."
  obtain hab : {a,b} ∈ 𝒫 (A ∪ B)
  Hint "***Good.*** Now remember: to say `\{{a},{b}} ∈ 𝒫 (A ∪ B)` is definitionally the same as saying `\{{a},{b}} ⊆ A ∪ B`. So let's `intro` the right stuff."
  intro x hx
  Hint "The hypothesis we just inroduced, namely `{hx}` is actually an `∨`-statement! Lean thinks of `{x} ∈ \{{a},{b}}` as being definitionally the same as saying `{x} = {a} ∨ {x} ∈ \{{b}}`. Let's use `obtain` to split into cases."
  obtain xa | xb := hx
  Hint "This goal seems straightforward. Clear it."
  left
  rw[xa]
  exact ha.left
  Hint "We know that `{x} ∈ \{{b}}` -- Lean sees this as definitionally equivalent to saying `{x} = {b}`. Let's use this info to try to prove the `right`-hand side of our disjunctive goal."
  right
  rw[xb]
  exact hb
  Hint "***Terrific.*** Let's rewrite the assumption `{hab}` to use `𝒫 A ∪ 𝒫 B` instead of `𝒫 (A ∪ B)`."
  rw[h] at hab
  Hint "Let's now use `obtain` to break down the assumption `{hab}` into cases."
  obtain T | F := hab
  Hint "Definitionally, the hypothesis `{T}` says `\{{a},{b}} ⊆  A`. Our goal is to show that `{b} ∈ A`. 👉 So let's use
  ```
  apply {T}
  ```
  "
  apply T
  Hint "Notice that our goal is now to prove that `{b} ∈ \{{a},{b}}`. For review, this is because the `apply` tactic is like saying *It suffices to show...*. In our case, to prove that `{b} ∈ A`, it suffices to prove that `{b} ∈ \{{a},{b}}` since we know that `\{{a},{b}} ∈ 𝒫 A`.

  Now, notice that `{b}` is equal to the `right`-hand member of the set `\{{a},{b}}`...
  "
  right
  Hint "Our goal is definitionally the same as `{b} = {b}`. How to clear it?"
  rfl
  Hint "Try to finish this level off on your own."
  obtain F' : a ∈ B
  apply F
  left
  rfl
  obtain F'' := ha.right
  contradiction


Conclusion ""

NewTactic by_cases
