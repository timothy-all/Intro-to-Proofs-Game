import Game.Metadata

World "TylerWorld"
Level 1

Title "Proving statements of the form `P → Q`"

Introduction "The most fundamental proof technique is how to directly address goals of the form `P → Q`. To prove `P → Q`, we can assume `P` and try to deduce `Q`.

The `intro` tactic lets us assume `P` in this case."


Statement (n : Nat) : (n = 0) → 0 = n := by
  Hint "Write `intro h` to assume that `n = 0`. Lean will give this statement the name `h`."
  intro h
  Hint "Since we know `n = 0`, we can substitute the `n` in the goal with `0` by using `rw h`."
  rw [h]


Conclusion "Lean obviously knows that `0 = 0`, so the theorem is proved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl intro apply symm
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
