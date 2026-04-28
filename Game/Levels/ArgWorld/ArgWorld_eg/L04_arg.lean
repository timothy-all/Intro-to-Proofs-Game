import Game.Levels.ArgWorld.ArgWorld_eg.L03_arg

World "ArgWorld_eg"
Level 4

Title "Example 4"

Introduction "
### **Level 4**
"

set_option pp.parens true


Statement (P Q R S T U: Prop) (h1 : (¬ P ∨ Q) → R) (h2 : R → (S ∨ T)) (h3: ¬ S ∧ ¬ U) (h4 : ¬ U → ¬ T) : P ∧ ¬ Q:= by
  obtain nT := h4 h3.right
  rw[Contrapositive,Not_or] at h2
  obtain nR := h2 (And.intro h3.left nT)
  rw[Contrapositive,Not_or,Not_not] at h1
  exact (h1 nR)

Conclusion ""
