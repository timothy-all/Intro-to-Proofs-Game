import Game.Levels.SetWorld.L14_set

World "SetWorld"
Level 15

Title "The Power Set"

Introduction "
# **Level 15: Power Sets**
Given a set `A : Set u`, the **power set** of `A`, denoted `𝒫 A` is defined as follows:
```
𝒫 A := {s : Set u | s ⊆ A}
```
Our current goal is a subset relation which we know is a unviersally quantified statement. Let's `intro` the appropriate stuff.
### **⌨ Typesetting tip**
In order to typeset the symbol `𝒫` use `\\powerset`.
"
open Set

/-- If $A$ is contained in $B$, then the power set of $A$ is contained in the power set of $B$.-/
Statement {u : Type} (A B: Set u) (h : A ⊆ B) : 𝒫 A ⊆ 𝒫 B := by
  intro C hC
  Hint "Great. Now, the membership proposition `B ∈ 𝒫 A` means the same thing as `B ⊆ A`. 👉 To rewrite `{C} ∈ 𝒫 A` in this form, try
  ```
  rw[mem_powerset_iff]
  ```
  "
  rw[mem_powerset_iff] at hC ⊢
  Hint "See if you can't finish the level! There's a theorem proven earlier in this world that you can use to one-shot it from here."
  exact Subseteq_trans hC h


Conclusion ""

NewDefinition Set.mem_powerset_iff
