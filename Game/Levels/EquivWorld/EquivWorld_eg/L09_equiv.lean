import Game.Levels.EquivWorld.EquivWorld_eg.L08_equiv
import Mathlib.Logic.Basic

World "EquivWorld_eg"
Level 9

Title "Exclusive-Or"

Introduction "
### **Level 9**
We introduce another (seemingly) new connective known as **exclusive-or**, denoted `⊻`. Here's how it is defined in Lean:
```
xor_def : P ⊻ Q ↔  (P ∧ ¬Q) ∨ (Q ∧ ¬P)
```
### **⌨ Typesetting-tip**
In order to typeset the symbol `⊻` type `\\veebar`.
"

set_option pp.parens true

infix:70 " ⊻ " => Xor'

Statement (P Q R : Prop) : ((P ⊻ Q) → R) ↔ ( (P ↔ Q) ∨ R) := by
  rw[xor_def]
  Hint "You might find it handy to also rewrite the `↔` on the right-hand side (at some point). 🔍 Check out the entry for `iff_def` in the **Definitions** tab."
  rw[Imp_iff_not_or]
  rw[Not_or]
  rw[Not_and,Not_and]
  rw[Not_not,Not_not]
  rw[← Imp_iff_not_or, ← Imp_iff_not_or]
  rw[← iff_def]


Conclusion ""

NewDefinition xor_def iff_def
