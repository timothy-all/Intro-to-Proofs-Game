import Game.Metadata

World "TylerWorld"
Level 3

Title "Hello World"

Introduction "To be able to use implications as givens, we can apply **Modus Ponens**. Modus ponens is a fancy name for the fact that if you know `P` and you know `P → Q`, then `Q` must also be true.
In this level, we will see how to apply modus ponens.
"

Statement (P Q: Prop) : (P ∧ (P → Q)) → Q := by
  sorry

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl intros
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
