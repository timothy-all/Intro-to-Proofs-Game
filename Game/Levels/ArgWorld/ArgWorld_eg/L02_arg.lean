import Game.Levels.ArgWorld.ArgWorld_eg.L01_arg

World "ArgWorld_eg"
Level 2

Title "Conditional Proof"

Introduction "
### **Level 2**
This argument is sometimes called the law of **Conditional Proof**. It is strongly related to currying...
"

/-- If `P` and `Q` are true and `P` implies `Q` implies `R`, then it must be that `R` is true.-/
Statement (P Q R: Prop) (h₁ : P ∧ Q) (h₂ : P → (Q → R)) : R := by
  rw[← Curry] at h₂
  exact h₂ h₁

Conclusion ""
