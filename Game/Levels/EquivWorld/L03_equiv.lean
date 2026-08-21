import Game.Levels.EquivWorld.L02_equiv

World "EquivWorld"
Level 3

Title "Currying"

Introduction "
# **Level 3 : Currying**
Oftentimes, we'll have implications of the form
```
(h₁ ∧ h₂) → P
```
For programmatic purposes, this kind of proposition is better expressed in the following way:
```
h₁ → (h₂ → P)
```
This exercise demonstrates that this process of translating the first form into the second (called ***currying***) is logically valid.
### **⌨ Typesetting Tip**
In order to pretty-print subscripts like in `H₁` use `H\\_1`.
"

set_option pp.parens true


/-- An implication where the hypothesis is a chain of conjuntions is logically equivalent to a certain chain of implications. -/
Statement Curry (P Q R : Prop) : ((P ∧ Q) → R) ↔ (P → (Q → R)) := by --currying
  rw[Imp_iff_not_or]
  Hint "That was a good first step. You might want to apply the **Conditional Law** codified in `Imp_iff_not_or` two more times. You can do this in one step with:
  ```
  rw[Imp_iff_not_or,Imp_iff_not_or]
  ```
  "
  rw[Imp_iff_not_or,Imp_iff_not_or]
  Hint "🔍 Check out two freshly unlocked laws of logic in the **Theorems** tab, namely `Not_and` and `Or_assoc`."
  rw[Not_and]
  rw[Or_assoc]

Conclusion "Currying is *extensively* used throughout Lean. We'll point out why when the time comes."

NewTheorem Not_and Or_assoc
