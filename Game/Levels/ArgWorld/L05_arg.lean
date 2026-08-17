import Game.Levels.ArgWorld.L04_arg

World "ArgWorld"
Level 5

Title "And-constructor"

Introduction "
### **Level 5**
In this level, we'll learn how to glue a couple known assumptions together with the `∧` connective.
"

set_option pp.parens true


Statement (P Q R : Prop) (hPQ : P → Q) (hPR : P → R) (hP : P) : (Q ∧ R) := by
  Hint "First, let's `obtain` the hypotheses `hQ : Q` and `hP : P`."
  obtain hQ := hPQ hP
  obtain hR := hPR hP
  Hint "Now, we just need to connect the assumptions `hQ` and `hR` with `∧`. The *constructor* that does this is `And.intro`. 🔍 Check out entry for `And.intro` in the **Definitions** tab. 👉 In our particular case, try:
  ```
  obtain hQR := And.intro {hQ} {hR}
  ```
  "
  obtain hQR := And.intro hQ hR
  Hint "Now we have `{hQR} : Q ∧ R`. Almost done..."
  exact hQR
  -- one shot with : exact And.intro (hPQ hP) (hQR hR)

Conclusion "***💪 Challenge:*** You can one-shot this level."

NewDefinition And.intro
