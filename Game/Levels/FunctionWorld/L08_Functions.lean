import Game.Levels.FunctionWorld.L07_Functions


World "FunctionWorld"
Level 8

Title "function"

Introduction "A bijection is a function that is both one-to-one and onto. We'll bundle these properties together into `isBijection`; check your inventory. Prove that the identity function is a bijection to get a bit of practice. This will be useful in CardinalityWorld later, so this fact will be added to your inventory too!"



Statement Fun_identity_bij {u: Type*} : isBijection (Rel_id u) := by
  constructor
  intro a b c hac hbc
  rw [hac, hbc] --rfl not needed
  intro b
  exist b
  rfl


Conclusion "."

NewDefinition isBijection
NewTheorem Fun_identity_bij
