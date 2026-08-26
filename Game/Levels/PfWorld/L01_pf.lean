import Game.Levels.SetWorld
import Game.Levels.SetWorld.SetWorld_eg
import Game.Levels.PfWorld.Metadata_pfworld
import Game.Levels.PfWorld.pf_docs

World "PfWorld"
Level 1

Title "Definition unravelling"

Introduction "
# **Level 1**
Let's start with a direct proof. This is a statement about even integers. So first and foremost, we should recall what does it mean to say that an integer is *even*. 👉 Toward that end, try:
```
rw[isEven] at hx hy
```
This will apply the definition of *even* at the hypotheses `hx` and `hy`. 🔍 You can check out the definitions for `isEven` and `isOdd` in the **Definitions** tab.
"

/-- The sum of two even integers is even.-/
Statement (x y : ℤ) (hx : isEven x) (hy: isEven y) : isEven (x + y) := by
  rw[isEven] at hx hy
  Hint "So `isEven` is truly an existential statement. We should `obtain` witnesses to these existentials."
  obtain ⟨k,hk⟩ := hx
  obtain ⟨l,hl⟩ := hy
  Hint "Our goal is also an existential statement. So in order to prove this existential statement, we need to profer a witness."
  exist k+l
  Hint "Excellent. Now try
  ```
  rw[{hk},{hl}]
  ```
  "
  rw[hk,hl]
  Hint "We're almost done. In order to alleviate us from the burdens of formally manipulating easy to verify algebraic statements like the current goal, we've made a custom tactic ...
  ### **❯ The `simplify` tactic**
  The `simplify` tactic will attempt to clear the goal by applying *very* basic simplification rules to the goal. For example, if the goal is `⊢ x * (y + z) = x * y + x * z`, then `simplify` will clear it. 👉 In our case, try:
  ```
  simplify
  ```
  "
  simplify

Conclusion "### **💡 Pro-tip:**
The first line `rw[isEven] at hx hy` wasn't necessary. Lean knows that `isEven` is definitionally an existential statement. Here's the shorter version of this same proof:
```
obtain ⟨k,hk⟩ := hx
obtain ⟨l,hl⟩ := hy
exist k+l
rw[hk,hl]
simplify
```
**🌐 How to translate.** Here's how to translate this Lean proof into a human-readable proof line-by-line.
> *Since $x,y$ are even, let $k$ be an integer such that $2k = x$ and let $l$ be an integer such that $2l = y$.*
> These are the lines `obtain ⟨k,hk⟩ := hx` and `obtain ⟨l,hl⟩ := hy`.
>
> *Consider the integer $k+l$. We aim to prove that $x + y = 2(k+l)$.*
>
> This is the line `exist k + l`.
>
> *By substitution, this is equivalent to showing $2k + 2l = 2(k + l)$.*
>
> This is the line `rw[hk,hl]`.
>
> *After simplifying, this follows by reflexitivity.*
>
> This is the line `simplify`.
>
There are smoother ways to write this proof, but this is the most logically direct translation from Lean to human-readable.
"


NewDefinition isEven isOdd
NewTactic simplify
