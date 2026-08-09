import Game.Levels.EquivWorld
import Game.Levels.EquivWorld.EquivWorld_eg.equiv_eg_docs

World "EquivWorld_eg"
Level 1

Title "Proof-by-cases"

Introduction "
### **Level 1**
This logical equivalence is sometimes called **Proof by cases**. We'll use this (and variants thereof) a lot in the future (with the help of a tactic). It basically tells us how to approach proofs where we have a hypothesis in the form a disjunction.

We'll need two new laws of logic to pass this level. 🔍 Check out the entries for `Not_or` and `Or_and_left`.
"

set_option pp.parens true

Statement (P Q R : Prop) : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  rw[Imp_iff_not_or]
  rw[Not_or]
  rw[Or_comm]
  rw[Or_and_left]
  rw[Or_comm]
  rw[← Imp_iff_not_or]
  rw[Or_comm]
  rw[← Imp_iff_not_or]

Conclusion ""

NewTheorem Not_or Or_and_left

example (P Q R : Prop) : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  calc
    ((P ∨ Q) → R) ↔ (¬ (P ∨ Q) ∨ R) := by rw[Imp_iff_not_or]
    _ ↔ R ∨ ¬ (P ∨ Q) := by rw[Or_comm]
    _ ↔ R ∨ (¬ P ∧ ¬ Q) := by rw[Not_or]
    _ ↔ (R ∨ ¬ P) ∧ (R ∨ ¬ Q) := by rw[Or_and_left]
    _ ↔ (¬ P ∨ R) ∧ (R ∨ ¬ Q) := by rw[Or_comm]
    _ ↔ (P → R) ∧ (R ∨ ¬ Q) := by rw[← Imp_iff_not_or]
    _ ↔ (P → R) ∧ (¬ Q ∨ R) := by rw[Or_comm]
    _ ↔ (P → R) ∧ (Q → R) := by rw[← Imp_iff_not_or]
