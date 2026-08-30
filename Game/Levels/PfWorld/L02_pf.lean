import Game.Levels.PfWorld.L01_pf
--import Mathlib.Tactic.Ring

World "PfWorld"
Level 2

Title "Proof by contraposition"

Introduction "
# **Level 2: Contraposition**
Oftentimes we need to use multiple strategies to prove a theorem. First and foremost, our goal here is `⊢ x ∈ A → (x ∈ D → x ∉ B)`. Let's address the initial if-then statement directly with
```
intro hxA
```
"

/-- Suppose $A,B,C,D$ are sets, and suppose $A ∩ B ⊆ C \ D$. Let $x$ be a generic element of $u$. If $x ∈ A$ and $x ∈ D$, then $x ∉ B$.-/
Statement (u : Type*) (A B C D : Set u) (h : A ∩ B ⊆ C \ D) (x : u) : x ∈ A → (x ∈ D → x ∉ B) := by
  intro hxA
  Hint "Now our goal is `⊢ x ∈ D → x ∉ B`. Given that the conclusion of this if-then statement is negated, we might be tempted to try something more indirect here. We could use `rw[Contrapositive]`. Alternatively, there is the ...
  ### **❯ The `contrapose` tactic**
  The `contrapose` tactic will turn a goal of the form `⊢ P → Q` into `⊢ ¬ Q → ¬ P`. 👉 Give it a try with:
  ```
  contrapose
  ```
  "
  contrapose
  Hint "👉Let's get rid of the double negative with
  ```
  rw[Not_not]
  ```
  "
  rw[Not_not]
  Hint "Now, let's tackle ***this*** if then statement directly. Specifically, let's `intro` the hypothesis `x ∈ B`."
  intro hxB
  Hint "We now have the hypotheses `{hxA}` and `{hxB}`. Using `h`, we should be able to `obtain` the hypothesis that `x ∈ C \\ D`. And from there we're pretty much home free. See if you can't finish."
  obtain hx_diff := h (And.intro hxA hxB)
  exact hx_diff.right

Conclusion "### **💡 Pro-tip**
From the last hint, we could have one-shotted the goal with
```
exact (h (And.intro hxA hxB)).right
```
**🌐 How to translate.** The lines of this proof containing
```
contrapose
rw[Not_not]
intro hxB
```
 of this Lean proof can be translated with something like:
> *We aim to prove the contrapositive. Toward that end, suppose $x ∈ B$.*
"

NewTactic contrapose
