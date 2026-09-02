import Game.Levels.QuantifierWorld.L02_quant
--import Mathlib.Tactic.Use

World "QuantifierWorld"
Level 3

Title "Existential Generalization"

Introduction "
## **Level 3**
This valid argument is sometimes called **Existential Generalization**. It says that if you know that a predicate (like `P`) is true for some `a` of type `u`, then we can deduce that there exists an element `x` of type `u` such that `P x` is true. In order to prove this valid argument, we need a way to reckon with an existential goal in Lean. We need a new tactic ...
### **❯ The `exist` tactic**
The most direct way to prove an existential goal is to supply a **witness** to the statement. The `exist` tactic is handy in this regard. Specifically, 👉 try:
```
exist a
```
"

/-- This valid argument is called *Existential Generalization*. -/
Statement {u : Type*} (a : u) (P : u → Prop) (h : P a) : ∃ x, P x := by
  exist a
  Hint "See how our goal is now `⊢ P {a}` and `{a} : u` is a generic **Object** in our proof state? We're nearly done."
  exact h

Conclusion "The `exist` tactic supplies a *witness* to an existential goal; our job going forward is to prove that our witness truly satisfies the predicate.
### **🌐 How to translate**
In terms of translating Lean into a human-readable proof, it makes sense to translate a statement like `exist a` in this proof into
> *Consider the known element $a$.*"

NewTactic exist
