import Game.Levels.EquivWorld.L01_equiv

World "EquivWorld"
Level 2

Title "Contrapositives"

Introduction "
# **Level 2: Contrapositives**
Let's use the laws of logic to prove that the ***Contrapositive*** of an implication is logically equivalent to the original implication. 👉 To get going, let's use
```
rewrite[Imp_iff_not_or]
```
"

set_option pp.parens true


/-- The **contrapositive** of an implication is logically equivalent to the original implication.-/
Statement Contrapositive {P Q : Prop} : (P → Q) ↔ (¬ Q → ¬ P) := by
  rewrite[Imp_iff_not_or]
  Hint "***Good.*** Now, let's `rewrite` the other implication as well."
  rewrite[Imp_iff_not_or]
  Hint "Here's where our newly unlocked theorem `Not_not` can be handy. 🔍 Check out the entry for `Not_not` in the **Theorems** tab. 👉 In our situation, try
  ```
  rewrite[Not_not]
  ```
  "
  rw[Not_not]
  Hint "We're almost home. Let's take the time to introduce a new tactic ...
  ## **❯ The `rw` tactic**
  The `rw` tactic is identical to `rewrite` except that it automatically attempts to clear the goal with `rfl` at the end. Give it a try!
  "
  rw[Or_comm]


Conclusion "### **💡 Pro-tip**
We almost always use `rw` instead of `rewrite` -- this can often save us a line of Lean code."

NewTheorem Not_not
NewTactic rw
