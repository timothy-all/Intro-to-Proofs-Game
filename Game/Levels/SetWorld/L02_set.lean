import Game.Levels.SetWorld.L01_set

World "SetWorld"
Level 2

Title "⊆ is transitive"

Introduction "
# **Level 2**
The **subset** relation is transitive. This means that if $A ⊆ B$ and $B ⊆ C$, then $A ⊆ C$. Let's prove this in Lean. Our goal is to prove `A ⊆ C`. Remember: this is just short-hand for:
```
∀ x, x ∈ A → x ∈ C
```
Let's `intro` a generic variable, say `a`, and the assumption that `a ∈ A`.
"

/-- The subset relation is transitive. -/
Statement Subseteq_trans {u : Type*} {A B C: Set u} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  Branch
    intro a
    Hint "This is fine. But you could have introduced more! ⏮ Click the **Retry** button at the previous prompt and try
    ```
    intro a ha
    ```
    "
  intro a ha
  Hint "**Great.** We've introduced a generic element `{a}` and the hypothesis `{ha}`. We can clear the goal in one line if we're clever."
  exact hBC (hAB ha)


Conclusion "### **💡 Pro-tip**
If we have a goal like `⊢ A ⊆ B`, then the first line of our proof is (almost surely) `intro a ha`.

**🌐 How to translate.** In plain English, we translate a line like `intro a ha` into something like
> *Let $a$ be an arbitrary element of $A$.*
"
