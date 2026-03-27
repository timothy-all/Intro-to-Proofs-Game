import Game.Levels.ArgWorld.ArgWorld_eg.L03_arg

World "ArgWorld"
Level 4

Title "Test"

Introduction "
### **🤔 Level 4?**
"

set_option pp.parens true

/--
obtain doc
-/
TacticDoc obtain

Statement (P Q R S T U: Prop) (h1 : (¬ P ∨ Q) → R) (h2 : R → (S ∨ T)) (h3: ¬ S ∧ ¬ U) (h4 : ¬ U → ¬ T) : P ∧ ¬ Q:= by
  obtain nT := h4 h3.right
  rw[contrapositive,Not_or] at h2
  obtain nR := h2 (And.intro h3.left nT)
  rw[contrapositive,Not_or,Not_not] at h1
  exact (h1 nR)

Conclusion ""

NewTactic obtain
