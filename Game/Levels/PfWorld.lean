import Game.Metadata
import Game.Levels.PfWorld.L01_pf
import Game.Levels.PfWorld.L02_pf
import Game.Levels.PfWorld.L03_pf
import Game.Levels.PfWorld.L04_pf
import Game.Levels.PfWorld.L05_pf
import Game.Levels.PfWorld.L06_pf
import Game.Levels.PfWorld.L07_pf
import Game.Levels.PfWorld.L08_pf
import Game.Levels.PfWorld.L09_pf
import Game.Levels.PfWorld.L10_pf
import Game.Levels.PfWorld.L11_pf
import Game.Levels.PfWorld.L12_pf
import Game.Levels.PfWorld.L13_pf

World "PfWorld"
Title "Proof Strategy World"

Introduction "
# **Proof Strategy World**
So far, we've really only attempted so-called **direct proofs**. This is where our goal is of the form `⊢ P → Q` so we make `P` an **Assumption** (using the `intro` tactic) and then our goal becomes `⊢ Q`.

But there are many other proof strategies that can be more appropriate (given the situation) and easier to manage. In Lean, these proof strategies are realized through various **tactics** -- for example, `intro` is the tactic we use for a direct proof strategy. In this world, we'll learn about tactics that help implement the following proof strategies:
* **Indirect proofs:** proofs by contraposition, proofs by contradiction
* **Proofs involving quantifiers:** universally and existentially quantified statements
* **Proofs of conjunctions**: proofs of `∧` and `↔` statements
* **Proofs involving disjunctions:** proofs of `∨` statements, proof by cases
* **Existence and uniqueness proofs: proofs involving the quantifier `∃!`
>
We'll mostly learn by example here, but we'll justify our proof strategies along the way too. Let's get started!
"

Image "images/pf2.png"
