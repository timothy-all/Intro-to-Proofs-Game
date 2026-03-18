import Game.Levels.EquivWorld.L01_equiv

World "EquivWorld"
Level 2

Title "Test"

Introduction "
### **🤔 Level 2?**
Oftentimes, we'll have implications of the form
```
(H₁ ∧ H₂) → P
```
For programmatic purposes, this kind of proposition is better expressed in the following way:
```
H₁ → (H₂ → P)
```
This exercise demonstrates that this process of translating the first form into the second (called **currying**) is logically valid.
"

set_option pp.parens true

/-- Doc-/
TheoremDoc Or_assoc as "Or_assoc"

/-- Doc -/
TheoremDoc Not_and as "Not_and"

/-- Rewrite stuff-/
TacticDoc rw


Statement (P Q R : Prop) : ((P ∧ Q) → R) ↔ (P → (Q → R)) := by --currying
  rw[← Or_imp]
  Hint "That was a good first step. You might want to apply the **Conditional Law** codified in `Or_imp` two more times. You can do this in one step with:
  ```
  rewrite[← Or_imp,← Or_imp]
  ```
  Or even better ...
  ### **❯ The `rw` tactic**
  The `rw` tactic is the same as `rewrite` but it tries to apply `rfl` at the end to clear the goal. For this reason, we **almost always** use `rw` instead of `rewrite`. 👉 Try:
  ```
  rw[← Or_imp,← Or_imp]
  ```
  "
  rw[← Or_imp,← Or_imp]
  Hint "🔍 Check out two freshly unlocked laws of logic in the **Theorems** tab."
  rw[Not_and]
  rw[Or_assoc]


Conclusion ""

NewTheorem Not_and Or_assoc
NewTactic rw
