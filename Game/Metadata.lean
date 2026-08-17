import GameServer

open Classical

@[simp]
theorem Imp_iff_not_or (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) := by
  constructor
  intro
  by_cases hp : P
  right
  exact a hp
  left
  exact hp
  intro h
  intro hp
  rcases h
  contradiction
  exact h

theorem Contra (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  repeat rw[Imp_iff_not_or]
  rw[not_not]
  rw[Or.comm]

theorem Not_and (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  simp -- not_and_of_not_or_not

theorem Not_or (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  simp

theorem Or_comm (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  exact Or.comm

theorem And_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  exact And.comm

theorem And_assoc (P Q R : Prop) : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) := by
  exact and_assoc

theorem Or_assoc (P Q R : Prop) : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) := by
  exact or_assoc

theorem And_or_left (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  exact and_or_left

theorem Or_and_left (P Q R : Prop) : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) := by
  exact or_and_left

theorem Not_not (P : Prop) : ¬ ¬ P ↔ P := by
  exact not_not

theorem And_self (P : Prop) : (P ∧ P) ↔ P := by
  simp

theorem Or_self (P : Prop) : (P ∨ P) ↔ P := by
  simp

theorem And_true (P : Prop) : P ∧ True ↔ P := by
  simp

theorem True_and (P : Prop) : True ∧ P ↔ P := by
  simp

theorem Or_true (P : Prop) : P ∨ True ↔ True := by
  simp

theorem True_or (P : Prop) : True ∨ P ↔ True := by
  simp

theorem And_false (P : Prop) : P ∧ False ↔ False := by
  simp

theorem False_and (P : Prop) : False ∧ P ↔ False := by
  simp

theorem Or_false (P : Prop) : P ∨ False ↔ P := by
  simp

theorem False_or (P : Prop) : False ∨ P ↔ P := by
  simp

theorem Or_not_self (P : Prop) : P ∨ ¬ P ↔ True := by
  simp
  by_cases h : P
  repeat simp[h]

theorem Not_self_or (P : Prop) : ¬ P ∨ P ↔ True := by
  rw[or_comm]
  rw[Or_not_self]

theorem And_not_self (P : Prop) : P ∧ ¬ P ↔ False := by
  simp

-- Custom tactics

syntax "use! " term : tactic
macro_rules
  | `(tactic| use! $w) =>
      `(tactic| refine Exists.intro $w ?_; dsimp)
