import Game.Levels.ArgWorld.ArgWorld_eg.L01_arg

World "ArgWorld_eg"
Level 2

Title "Conditional Proof"

Introduction "
### **Level 2**
This argument is sometimes called the law of **Conditional Proof**. It is strongly related to currying...
"

/-- This valid argument is called the law of **Conditional Proof**.-/
Statement (P Q R: Prop) (hPandQ : P ∧ Q) (hPQR : P → (Q → R)) : R := by
  rw[← Curry] at hPQR
  exact hPQR hPandQ

Conclusion ""
