import Game.Levels.ArgWorld.ArgWorld_eg.L06_arg

World "ArgWorld_eg"
Level 7

Title "Example 5"

Introduction "
# **Level 7**
Here's another abstract example. This one has six component propositions! But don't get overwhelmed -- think in small steps and don't try to see the whole thing at once. For example, we might notice that `¬ T` can be deduced from what is assumed.
"

set_option pp.parens true


Statement (P Q R S T U: Prop) (h1 : (¬ P ∨ Q) → R) (h2 : R → (S ∨ T)) (h3: ¬ S ∧ ¬ U) (h4 : ¬ U → ¬ T) : P ∧ ¬ Q:= by
  obtain nT := h4 h3.right
  rw[Contrapositive,Not_or] at h2
  obtain nR := h2 (And.intro h3.left nT)
  rw[Contrapositive,Not_or,Not_not] at h1
  exact (h1 nR)

Conclusion "😭 To validate this argument with a truth-table would require 64 rows."
