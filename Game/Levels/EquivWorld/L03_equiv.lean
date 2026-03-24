import Game.Levels.EquivWorld.L02_equiv

World "EquivWorld"
Level 3

Title "Currying"

Introduction "
## **Level 3**
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

/--
Doc on currying
-/
TheoremDoc curry as "curry"

Statement curry (P Q R : Prop) : ((P ∧ Q) → R) ↔ (P → (Q → R)) := by --currying
  rw[← Or_imp]
  Hint "That was a good first step. You might want to apply the **Conditional Law** codified in `Or_imp` two more times. You can do this in one step with:
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
