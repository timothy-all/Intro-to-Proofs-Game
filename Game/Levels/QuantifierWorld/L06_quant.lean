import Game.Levels.QuantifierWorld.L05_quant


World "QuantifierWorld"
Level 6

Title "Negated Existential"

Introduction "
# **Level 6**
A negated `∃`-statement turns into an `∀`-statement and vice versa. This follows (essentially) from DeMorgan's law (remember: `∀` statements are like gigantic `∧`-statements). The theorem `Not_exists` codifies this relationship for us; 🔍 check out the entry for `Not_exists` in the **Theorems** tab. 👉 For our purposes here, try
```
rw[Not_forall] at h
```
"

Statement {u : Type*} (P : u → Prop) (h : ¬ ∃ x, P x) : ∀ x, ¬ P x := by
  rw[Not_exists] at h
  Hint "See how `h` is now the hypothesis `h : ∃ x, ¬ P x`? We're almost done."
  exact h

Conclusion "### **💡 Pro-tip**

"

--NewTactic push_neg
NewTheorem Not_exists

/-
There is a tactic that will **push negatives** through quantified statements. Conveniently that tactic is called ...
### **❯ The `push_neg` tactic**
The tactic `push_neg` will push negations through the target. In our case, 👉 try:
```
push_neg at h
```
-/
