import Game.Metadata
import Game.Levels.EquivWorld.equiv_docs

World "EquivWorld"
Level 1

Title "Intro to Lean"

Introduction "
# **Level 1 : Intro to L∃∀N**
We've unlocked two theorems for this first level, namely: `Or_comm` and `Imp_iff_not_or`. 🔍 Check out the entries for these theorems in the **Theorems** tab.

The conditional law says that `P → Q` is logically equivalent to `¬ P ∨ Q`. This looks **very** close to that statement. We might start by ***rewriting*** the right-hand side of our goal using `Or_comm`.


  ## **❯ The `rewrite` tactic**
  In order to apply ***rewrites*** (or substitutions) in Lean, we use the `rewrite` tactic. 🔍 Check out the entry for `rewrite` in the **Tactics** tab for details. 👉 In this specific case, try
  ```
  rewrite[Or_comm]
  ```
  This will apply the **Commutative Law** for `∨` at the first instance in the goal where it is applicable (namely, the right-hand side in this case).
"

set_option pp.parens true

/-- The implication `P → Q` is logically equivalent to `Q ∨ ¬ P`.-/
Statement (P Q : Prop) : (P → Q) ↔ (Q ∨ ¬ P) := by
  rewrite[Or_comm]
  Hint "We should now `rewrite` the left-hand side of our goal using the **Conditional Law**. 🔍 Check the **Theorems** tab to find the appropriate theorem in the inventory."
  rewrite[Imp_iff_not_or]
  Hint "
  ### **❯ The `rfl` tactic**
  Our goal is currently `(P → Q) ↔ (P → Q)` ... this is true by reflexitivity! The tactic that clears the goal is `rfl`. 🔍 Check out the entry for `rfl` in the **Tactics** tab. 👉 In our case, try:
  ```
  rfl
  ```
  "
  rfl

Conclusion "
### ***🥳 Congrats!***
You beat the first level! We'll add more **Theorems** (known logical equivalences) as we progress through the world.
"

NewTactic rewrite rfl
NewTheorem Imp_iff_not_or Or_comm
