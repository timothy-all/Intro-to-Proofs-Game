import Game.Levels.EquivWorld

World "ArgWorld"
Level 1

Title "Modus Ponens"

Introduction "
## **Level 1**
Lean natively is aware of the valid argument known as **modus ponens**. In fact, Lean has a funny way of interpreting...
## **Implications as functions**
We have `hPQ : P → Q`. We can think of this implication as being a function, whose input is (a proof of) `P` and whose output is (a proof of) `Q`. So we should be able to obtain a new hypothesis in our situation here, namely `hQ : Q`. But how to do this?
"

/--
Exact doc
-/
TacticDoc exact

/--
Obtain doc
-/
TacticDoc obtain

Statement (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  Hint "### **❯ The `obtain` tactic**
  The `obtain` tactic allows us to introduce new assumptions into our current proof *as long as* we supply proofs (in the current context) of those assumptions. 👉 Try the following basic usage:
  ```
  obtain hQ := hPQ (hP)
  ```
  **Note:** the space between `hPQ` (the *function*) and `hP` (the *input*). Since the argument here is atomic, the parentheses are optional. So even the following ought to work:
  ```
  obtain hQ := hPQ hP
  ```
  "
  obtain hQ := hPQ (hP)
  Hint "Notice that we now have `hQ : Q` as an assumption. But this is our goal too! What finishing tactic will clear the level?
  ### **❯ The `exact` tactic**
  The tactic `exact e` will clear the goal if the goal matches the type of `e`. 👉 In our case, try
  ```
  exact hQ
  ```
  "
  exact hQ

Conclusion ""

NewTactic exact obtain
