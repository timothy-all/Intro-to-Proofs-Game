import Game.Levels.ArgWorld.ArgWorld_eg.L01_arg

World "ArgWorld_eg"
Level 2

Title "Conditional Proof"

Introduction "
### **Level 2**
This argument is sometimes called the law of **Conditional Proof**. It might help to apply a
"


Statement (P Q R: Prop) (hP : P) (hQ : Q) (h : P → (Q → R)) : R := by
  rw[← Curry] at h
  exact h (And.intro hP hQ)

Conclusion ""
