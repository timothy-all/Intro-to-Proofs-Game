import Game.Metadata

World "RelationWorld"
Level 1

Title "Cartesian products"

Introduction "Verify what it means for `x` to **not** be in a Cartesian product"


Statement {x} (hxA : ¬ (x ∈ A ∪ B)) : ¬ x ∈ A ∧ ¬ x ∈ B := by
  Hint "Write `intro h` to assume that `n = 0`. Lean will give this statement the name `h`."
  intro h
  Hint "Since we know `n = 0`, we can substitute the `n` in the goal with `0` by using `rw h`."
  rw [h]


Conclusion "Lean obviously knows that `0 = 0`, so the theorem is proved.

**Warning:** Ending up at `0 = 0` here is only fine because `rw` applies a logical equivalence (or equality). Applying one-directional implications works differently, as we will see in the next level."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl intro apply symm
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
