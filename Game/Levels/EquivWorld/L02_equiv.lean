import Game.Levels.EquivWorld.L01_equiv

World "EquivWorld"
Level 2

Title "Contrapositives"

Introduction "
## **Level 2**
Let's use the laws of logic to prove that the **contrapositive** of an implication is logically equivalent to the original implication. We'll need the **Double Negation Law** (the theorem `Not_not`). 🔍 Check out the unlocked entry for `Not_not` in the **Theorems** tab.
"

set_option pp.parens true

/--
This is the **Double Negation Law**. It says that

$$ ¬ ¬ P ↔ P $$
-/
TheoremDoc Not_not as "Not_not"

/--
An implication is logically equivalent to its contrapositive.
-/
TheoremDoc contrapositive as "contrapositive"

/--
The tactic `rw` is the same as `rewrite` except it automatically attempts to clear the goal with `rfl` at the end. This can often save us a line.
-/
TacticDoc rw

Statement contrapositive (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  Hint (hidden := true) "Maybe we tried
  ```
  rewrite[Or_imp]
  ```
  and it didn't work. Why? Check the entry for `Or_imp` in the **Theorems** tab. Note that
  ```
  Or_imp (P Q : Prop) : (¬ P ∨ Q) ↔ (P → Q)
  ```
  We want to apply this law ***in reverse***. In other words, we want to rewrite `P → Q` to `¬ P ∨ Q`. 👉 In order to do this, try the syntax:
  ```
  rewrite[← Or_imp]
  ```
  ### **⌨ Typesetting Tip**
  In order to get the pretty printed left arrow `←` use `\\left`. You can also use `<-` instead."
  rewrite[← Or_imp, ← Or_imp]
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
