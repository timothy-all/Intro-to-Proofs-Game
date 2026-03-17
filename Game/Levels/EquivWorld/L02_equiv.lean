import Game.Levels.EquivWorld.L01_equiv

World "EquivWorld"
Level 2

Title "Test"

Introduction "
### **🤔 Level 2?**

"

set_option pp.parens true

/-- Doc-/
TheoremDoc Or_assoc as "Or_assoc"

/-- Doc -/
TheoremDoc Not_and as "Not_and"

/-- Rewrite stuff-/
TacticDoc rw

theorem test1 (P Q R : Prop) : (P → (Q ∨ R)) ↔ (¬ R → (P → Q)) := by
  rw[← Or_imp,← Or_imp]
  rw[Not_not]
  rw[← Or_imp]
  rw[Or_comm Q] -- tricky since or_comm has implicit arguments
  rw[← Or_assoc]
  rw[Or_comm (¬ P)] -- ditto
  rw[Or_assoc]

theorem test2 (P Q : Prop) : (¬ ((P ∨ Q) ∧ (¬ P ∧ (Q → P)))) ↔ True := by
  rw[Not_and]
  rw[← Or_imp]
  rw[Not_and]
  rw[Not_or (¬ Q)]
  rw[Not_not,Not_not]
  rw[Or_and_left]
  rw[Or_not_self]
  rw[And_true]
  rw[Or_comm]
  rw[Or_not_self]

theorem test3 (P Q R : Prop) : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  rw[← Or_imp]
  rw[Not_or]
  rw[Or_comm]
  rw[Or_and_left]
  rw[Or_comm]
  rw[Or_imp]
  rw[Or_comm]
  rw[Or_imp]

Statement (P Q R : Prop) : ((P ∧ Q) → R) ↔ (P → (Q → R)) := by --currying
  rw[← Or_imp,← Or_imp,← Or_imp]
  rw[Not_and]
  rw[Or_assoc]


theorem test5 (P Q : Prop) : (P → Q) ↔ (P ∧ Q) ∨ ¬ P := by
  rw[← Or_imp]
  rw[Or_comm _ (¬ P)]
  rw[Or_and_left]
  rw[Or_comm (¬ P) P]
  rw[Or_not_self]
  rw[true_and]



Conclusion ""

NewTheorem Not_and Or_assoc
NewTactic rw
