import Game.Levels.EquivWorld.L01_equiv

World "EquivWorld"
Level 2

Title "Contrapositives"

Introduction "
## **Level 2**
Let's use the laws of logic to prove that the **contrapositive** of an implication is logically equivalent to the original implication. We'll need the **Double Negation Law** (the theorem `Not_not`). 🔍 Check out the unlocked entry for `Not_not` in the **Theorems** tab.
"

set_option pp.parens true



Statement contrapositive (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  rewrite[Imp_iff_not_or, Imp_iff_not_or]
  Hint "Here's where our newly unlocked theorem can be handy."
  rw[Not_not]
  Hint "We're almost home. Let's introduce a new tactic ...
  ### **❯ The `rw` tactic**
  The `rw` tactic is identical to `rewrite` except that it automatically attempts to clear the goal with `rfl` at the end. This can often save us a line of Lean code. Give it a try!
  "
  rw[Or_comm]


Conclusion ""

NewTheorem Not_not
NewTactic rw
