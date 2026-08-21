import Game.Levels.ArgWorld
import Game.Levels.ArgWorld.ArgWorld_eg
import Game.Levels.QuantifierWorld.quant_docs
--import Mathlib.Tactic.TypeStar

World "QuantifierWorld"
Level 1

Title "Universal specification"

Introduction "
# **Level 1**
This valid argument is known as *Universal Specification*. More precisely, we have the assumption `h: ∀ x, P x`, and we wish to prove that `P a` is true where `a` is some element of type `u`. How do we use a universally quantified statement as an assumption? Lean has a funny (but familiar) way of thinking about such an assumption...
### **Universal statements as functions**
Lean considers the assumption `h: ∀ x, P x` sort of like a function. The input is `x` and element of type `u`. The output is (a proof of) the proposition `P x`. In our case, 👉 try:
```
obtain this := h a
```
"

variable {u : Type}

/-- This valid argument is known as *Universal Specification*. -/
Statement (P : u → Prop) (a : u) (h : ∀ x, P x) : P a := by
  obtain this := h a
  Hint "Note that `{this} : P a` is now known. The `exact` tactic ought to help us clear the goal now."
  exact this

Conclusion "### **💡 Pro-tip**
We could have one-shotted this level with `exact h a`.
### **🌐 How to translate**
To translate a statement like `obtain this := h a` in this proof into something human readable, you might use:
> *We get that $P a$ is true since we know that for all $x$ of type $u$, $P x$ is true, and $a$ is an element of type $u$.*
"
