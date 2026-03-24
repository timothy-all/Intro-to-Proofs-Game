import Game.Levels.EquivWorld.L03_equiv

World "EquivWorld"
Level 4

Title "Proof-by-cases"

Introduction "
### **Level 4**
This logical equivalence is sometimes called **Proof by cases**. We'll use this a lot in the future. It basically tells us how to approach proofs where we have a hypothesis in the form a disjunction. We'll need two new laws of logic to pass this level. 🔍 Check out the entries for `Not_or` and `Or_and_left`.
"

set_option pp.parens true

/--
This is half of **DeMorgan's Law**. It says that

$$¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)$$
-/
TheoremDoc Not_or as "Not_or"

/--
This is half of the **Distributive Law**. It says that

$$(P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))$$
-/
TheoremDoc Or_and_left as "Or_and_left"

Statement (P Q R : Prop) : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  rw[← Or_imp]
  rw[Not_or]
  rw[Or_comm]
  rw[Or_and_left]
  rw[Or_comm]
  rw[Or_imp]
  rw[Or_comm]
  rw[Or_imp]


Conclusion ""

NewTheorem Not_or Or_and_left
