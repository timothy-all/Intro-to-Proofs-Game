import Game.Levels.ArgWorld.L04_arg

World "ArgWorld"
Level 5

Title "Law of the syllogism"

Introduction "
### **Level 5**
The valid argument of this level is sometimes called the law of the **syllogism**.
"

set_option pp.parens true

/--
Tactic intro
-/
TacticDoc intro

Statement (P Q R : Prop) (hPQ : P → Q) ( hQR : Q → R) : (P → R) := by
  Hint "We wish to prove that `P → R` -- o ur goal, itself, is an implication. We know that implications are true by default if the hypothesis is false. So we might as well assume that `P` is true (otherwise `P → Q` is definitely true). How do we do this in Lean?
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
