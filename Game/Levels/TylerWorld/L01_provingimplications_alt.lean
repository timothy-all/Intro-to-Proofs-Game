import Game.Metadata

World "TylerWorld"
Level 2

Title "Proving statements of the form `P → Q`"

Introduction "The most fundamental proof technique is how to directly address goals of the form `P → Q`. To prove `P → Q`, we can assume `P` and try to deduce `Q`.

The `intro` tactic lets us assume `P` in this case."


Statement (n : Nat) : (n = 0) → 0 = n := by
  Hint "Write `intro h` to assume that `n = 0`. Lean will give this statement the name `h`."
  intro h
  Hint "We know that we can write equalities in any order; this is the **symmetric** property of equality. Lean calls this `symm` - write that to flip the equality's order."
  symm
  Hint "We now have to observe that we've proven what has been asked of us. `h` is now the goal, so by writing `exact h`, we tell Lean that we've established the goal."
  exact h

Conclusion "This matches, line by line, with the following proof of the statement in English:

Suppose n = 0. We will prove 0 = n.
Since n = 0 and equality is symmetric, 0 = n.
QED."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl intro apply symm exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
