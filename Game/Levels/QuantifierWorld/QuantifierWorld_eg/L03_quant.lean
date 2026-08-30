import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L02_quant

World "QuantifierWorld_eg"
Level 3

Title "Example 3"

Introduction "
# **Level 3**
This level shows that `∀ x, ∀ y...` is the same as `∀ y, ∀ x`. For that reason, we often just right `∀ x y, ...`.
"


/-- Universal quantifiers commute with themselves.-/
Statement {u : Type*} (P : u → u → Prop) : (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
  intro h y x
  exact h x y


Conclusion "🤔 Is it true that `∀ x, ∃ y` is the same as `∃ y, ∀ x`? No! Why? Think of a counter-example."
