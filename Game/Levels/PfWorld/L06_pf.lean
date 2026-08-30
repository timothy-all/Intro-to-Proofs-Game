import Game.Levels.PfWorld.L05_pf

World "PfWorld"
Level 6

Title "Biconditionals"

Introduction "
# **Level 6: Biconditionals**
This proof seems straightforward enough. But we'll need the `constructor` tactic again.
>
First, let's recall what it means for sets to be equal. 👉 Try
```
rw[set_eq_iff]
```
"

/-- If $A ⊆ B$ and $B ⊆ A$, then $A = B$.-/
Statement Double_inclusion {u : Type*} (A B : Set u) (hAB : A ⊆ B) (hBA : B ⊆ A): A = B := by
  rw[set_eq_iff]
  Hint "Let's `intro x` to reckon with the universal quantifier."
  intro x
  Hint "Our goal is a **biconditional** statement (an *iff*) namely `x ∈ A ↔ x ∈ B`. Logically, this is equivalent to
  ```
  (x ∈ A → x ∈ B) ∧ (x ∈ B → x ∈ A)
  ```
  The `constructor` tactic will split our goal into two subgoals accordingly. 👉 Try it out with
  ```
  constructor
  ```
  "
  constructor
  Hint "Our *Active Goal* is `⊢ x ∈ A → x ∈ B` while *Goal 2* is `⊢ x ∈ B → x ∈ A`. See if you can't finish from here."
  intro hxA
  exact hAB hxA
  intro hxB
  exact hBA hxB

Conclusion "### **💡 Pro-tip**
The biconditional statement that we proved in Logical Equivalence World were easy -- they could all be handled by substitution (i.e. the `rw` tactic). But, in general, the proof of the **forward** direction of a biconditional (that being `P → Q`) can look ***a lot*** different than the proof of the **backward** direction of a biconditional (that being `Q → P`)."
