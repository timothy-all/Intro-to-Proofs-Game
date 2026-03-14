import GameServer
-- import Mathlib.Tactic.Common

open Classical

@[simp]
theorem not_or_imp (P Q : Prop) : (¬ P ∨ Q) ↔ (P → Q) := by
  constructor
  intro h hP
  rcases h with nP | hQ
  contradiction
  exact hQ
  intro h
  by_cases hP : P
  exact Or.inr (h hP)
  exact Or.inl hP

theorem contra (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  intro h nQ
  by_cases hP : P
  exfalso
  exact nQ (h hP)
  exact hP
  intro h hP
  by_cases hQ : Q
  exact hQ
  exfalso
  exact (h hQ) hP

theorem DeMorgan_not_and (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  simp -- not_and : ¬ (p ∧ q) ↔ (p → ¬ q)

theorem DeMorgan_not_or (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  simp -- not_or :

/- Commutativity/Associativity is already defined via :
* and_comm/And.comm is already defined
* or_comm/Or.comm is already defined
* and_assoc
* or_assoc
-/

/- Distributive laws are already defined as
* and_or_left
* and_or_right
* or_and_left
* or_and_right
-/

/- Double negation is already defined as Classical.not_not -/

/- Classical.not_imp : ¬ (a → b) ↔ (a ∧ ¬ b) -/

/- Idempotent laws are also define `and_self` and `or_self` -/

/- Tautology/Contradiction laws are:
* and_true
* or_true
* and_false
* or_false
-/

theorem or_not_self (P : Prop) : P ∨ ¬ P ↔ True := by
  constructor
  intro h
  simp
  intro h
  by_cases hP : P
  exact Or.inl hP
  exact Or.inr hP

theorem not_self_or (P : Prop) : ¬ P ∨ P ↔ True := by
  rw[or_comm]
  rw[or_not_self]

theorem not_not (P : Prop) : ¬ ¬ P ↔ P := by
  simp


open Lean Elab Tactic

syntax "by_contra" (ppSpace binderIdent)? : tactic

macro_rules
  | `(tactic| by_contra $h:binderIdent) =>
      `(tactic| false_or_by_contra; rename _ => F; rename_i $h:binderIdent) --hack
  | `(tactic| by_contra) =>
      `(tactic| false_or_by_contra; rename _ => F) --hack
