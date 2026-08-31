import Game.Levels.EquivWorld.L05_equiv

World "EquivWorld"
Level 6

Title "Negated Implication"

Introduction "
# **Level 6: Negated Implication**
The negation of $P → Q$ is logically equivalent to saying $P ∧ ¬ Q$. This one is useful enought that we name for future use.
"

set_option pp.parens true

/-- The negation of $P → Q$ is equivalent to $P ∧ ¬ Q$.-/
Statement Not_imp (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q):= by
  rw[Imp_iff_not_or]
  rw[Not_or]
  rw[Not_not]

Conclusion "
"

NewTheorem Not_or
