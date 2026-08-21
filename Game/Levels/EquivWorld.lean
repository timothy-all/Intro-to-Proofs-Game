import Game.Metadata

import Game.Levels.EquivWorld.L01_equiv
import Game.Levels.EquivWorld.L02_equiv
import Game.Levels.EquivWorld.L03_equiv
import Game.Levels.EquivWorld.L04_equiv

World "EquivWorld"
Title "Logical Equivalence World"

Introduction "
# **Logical Equivalences**
Let `P` and `Q` be propositions (`Prop`). We say that `P` is **logically equivalent** to `Q` to mean that `P ↔ Q`, in other words, `P` is true whenever `Q` is true, moreover, `P` is false whenever `Q` is false. To put it succinctly, the truth tables for `P` and `Q` are identical. The graphic in this world illustrates two propositions that are ***not*** logically equivalent, namely `P ∨ (Q ∧ R)` and `(P ∨ Q) ∧ R`.

The game is aware of some well-known logical equivalences (ones we can easily check with truth-tables). Here's a small list (and what they're called in Lean):
* `Imp_iff_not_or : (P → Q) ↔ (¬ P ∨ Q)`
* `And_comm: (P ∧ Q) ↔ (Q ∧ P)`
* `Or_assoc: ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))`
* `Not_and: (¬ (P ∧ Q)) ↔ (¬ P ∨ ¬ Q)`.
You can 🔍 check out the entries for this theorems in the **Theorems** tab on the right. Everything at the moment is 🔒 locked (since we're just getting started), but you can still view the entries. Give it a try! And don't worry, you'll get used to the funny naming conventions.

The purpose of this world is to practice writing proofs of logical equivalences *using* known logical equivalences (like those above and others we'll learn about). Let's get started!
"
Image "images/equiv.png"
