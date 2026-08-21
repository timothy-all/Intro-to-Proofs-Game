import Game.Levels.ArgWorld.L05_arg

World "ArgWorld"
Level 6

Title "Law of the syllogism"

Introduction "
# **Level 6**
The valid argument of this level is sometimes called the law of the **Syllogism**.
"

set_option pp.parens true

/-- This valid argument is known as the *Law of the Syllogism*.-/
Statement (P Q R : Prop) (hPQ : P → Q) ( hQR : Q → R) : (P → R) := by
  Hint "We wish to prove that `P → R` -- our goal, itself, is an implication. We know that implications are true by default if the hypothesis is false. So we might as well assume that `P` is true (otherwise `P → Q` is definitely true). How do we do this in Lean?
  ### **❯ The `intro` tactic**
  To *introduce* the hypothesis of an implication as a goal, we use the `intro` tactic. 🔍 Check out the entry for `intro` in the **Tactics** tab. 👉 In our specific situation, try:
  ```
  intro hP
  ```
  "
  intro hP
  Hint "We now have the hypothesis `{hP} : P`. We can clear the level in one line now if we're clever..."
  exact hQR (hPQ hP)

Conclusion ""

NewTactic intro
