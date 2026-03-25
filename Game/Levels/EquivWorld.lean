import Game.Metadata

import Game.Levels.EquivWorld.L01_equiv
import Game.Levels.EquivWorld.L02_equiv
import Game.Levels.EquivWorld.L03_equiv
--import Game.Levels.EquivWorld.L04_equiv
--import Game.Levels.EquivWorld.L05_equiv
--import Game.Levels.EquivWorld.L06_equiv
--import Game.Levels.EquivWorld.L07_equiv

World "EquivWorld"
Title "Logical Equivalence World"

Introduction "
# **Logical Equivalences**
Let `P` and `Q` be propositions (`Prop`). We say that `P` is **logically equivalent** to `Q` to mean that `P ↔ Q`, in other words, `P` is true whenever `Q` is true, moreover, `P` is false whenever `Q` is false. To put it succinctly, the truth tables for `P` and `Q` are identical. Here are a few well-known logical equivalences that we can check via truth-tables:
* **Conditional Law:** `(¬ P ∨ Q) ↔ (P → Q)`
* **Commutative Law:** `(P ∨ Q) ↔ (Q ∨ P)` and `(P ∧ Q) ↔ (Q ∧ P)`
* **Associative Law:** `((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))` and `((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
`
* **DeMorgan's Law:** `(¬ (P ∧ Q)) ↔ (¬ P ∨ ¬ Q)` and `(¬ (P ∨ Q)) ↔ (¬ P ∧ ¬ Q)`.

The purpose of this world is to practice writing proofs of logical equivalences *using* known logical equivalences (like those above and others we'll learn about). Let's get started!
"
Image "images/pic0.png"
