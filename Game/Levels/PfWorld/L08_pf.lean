import Game.Levels.PfWorld.L07_pf

World "PfWorld"
Level 8

Title "Goal management"

Introduction "
# **Level 8: Goal management**
We have another biconditional statement to wrangle here. 👉 So let's get going with
```
constructor
```
"

Statement (u : Type*) (F G : Set (Set u)) : ⋃₀ F ∩ ⋃₀ G ⊆ ⋃₀ (F ∩ G) ↔ ∀ A ∈ F, ∀ B ∈ G, A ∩ B ⊆ ⋃₀ (F ∩ G) := by
  constructor
  Hint "For the **forward** direction, we have a lot of objects/assumptions to `intro`. 👉 Let's start with
  ```
  intro h
  ```
  "
  intro h
  Hint "We now have a universal quantifier to deal with, namely `⊢ ∀ A ∈ F, ...`. At its core, this goal is `⊢ ∀ A : Set u, A ∈ F → ...`. 👉 So let's try
  ```
  intro A
  ```
  "
  intro A
  Hint "Notice how our goal is now an if-then statement. 👉 Let's introduce the hypothesis with
  ```
  intro hA
  ```
  "
  intro hA
  Hint "Second verse, same as the first."
  intro B
  intro hB
  Hint "We now have a subset relation as a goal. This is secretly a universally quantified statement. 👉 So let's introduce a generic variable with
  ```
  intro x
  ```
  "
  intro x
  Hint "Finally, our goal is another if-then. 👉 Let's introduce the hypothesis with
  ```
  intro hx
  ```
  "
  intro hx
  Hint "### **💡 Pro-tip**
  We could have `intro`ed all these items in one go with
  ```
  intro {h} {A} {hA} {B} {hB} {x} {hx}
  ```
  Though that can be hard to see without the benefit of hindsight.
  >
  Now, in light of assumption `{h}`, we realize at this point that to prove our goal, it **suffices** to prove that `x ∈ ⋃₀ F ∩ ⋃₀ G`. In order to implement this strategy we use...
  ### **❯ The `apply` tactic**
  If our goal is of the form `⊢ Q` and we have a hypothesis of the form `h : P → Q`, then `apply h` will transform the goal into `⊢ P`. 👉 In our case, try
  ```
  apply {h}
  ```
  "
  apply h
  Hint "Notice how our goal is now `⊢ x ∈ ⋃₀ F ∩ ⋃₀ G`. Here's what happened in the last step: the hypothesis `{h}` is definitionally
  ```
  {h} : ∀ x, x ∈ ⋃₀ F ∩ ⋃₀ G → x ∈ ⋃₀ (F ∩ G)
  ```
  So the line `apply {h}` unified our previous goal with the conclusion of `{h}`; subsequently, our new goal is the hypothesis of `{h}`.
  >
  Now, our goal is actually a `∧`-statement. 👉 So let's use
  ```
  constructor
  ```
  "
  constructor
  Hint "Our goal is now an *existential* statement. We need to profer a witness..."
  exist A
  Hint "Great. We might be tempted to use the `constructor` tactic again here. But we can save ourselves some time with ...
  ### **❯ The `refine` tactic **
  The refine tactic acts like a combination of `constructor` and `exact`. In our particular case, notice that the left-hand side of our goal is exactly `{hA}` while the right-hand side of our goal is exactly `{hx}.left`. 👉 So we can clear our goal with
  ```
  refine ⟨ {hA}, {hx}.left ⟩
  ```
  "
  refine ⟨hA,hx.left⟩
  Hint "Goal cleared! We now need to profer a witness to our current existential goal..."
  exist B
  Hint "Right on. Try to clear the current goal with `refine` similarly to how we did it before."
  refine ⟨hB,hx.right⟩
  Hint "Perfect. We now need to prove the **backward** implication. Let's `intro` all the things."
  intro h x hx
  Hint "Consider the assumption `{hx}`. This assumption is really just two existential statements glued together with `∧`. Use `obtain` to grab witnesses to these two individual existential statements. 👉 Specifically, try
  ```
  obtain ⟨A,hA,hxA⟩ := {hx}.left
  ```
  "
  obtain ⟨A,hA,hxA⟩ := hx.left
  Hint "OK. Now, in the same way, grab a witness to the other existential in `{hx}.right`."
  obtain ⟨B,hB,hxB⟩ := hx.right
  Hint "Let's use the assumption `{h}` to get a new assumption saying that
  ```
  A ∩ B ⊆ ⋃₀ (F ∩ G)
  ```
  "
  obtain hAB := h A hA B hB
  Hint "Great. Now, look at our goal and look at the assumption you just introduced, namely `{hAB}`. It ***suffices*** to prove that `x ∈ A ∩ B`. What tactic did we just learn about that could be helpful here?"
  apply hAB
  Hint "Almost home."
  exact And.intro hxA hxB

Conclusion ""

NewTactic refine apply
