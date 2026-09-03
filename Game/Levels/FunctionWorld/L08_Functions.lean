import Game.Levels.FunctionWorld.L07_Functions


World "FunctionWorld"
Level 8

Title "Functions 8"

Introduction "## **Level 8 : Bijections**

A bijection is a function that is both one-to-one and onto. We'll bundle these properties together into `isBijection`; 🔍 check your inventory. Prove that the identity function is a bijection to get a bit of practice."


/-- The identity function is a bijection.-/
Statement Fun_identity_bij {u: Type*} : isBijection (Rel_id u) := by
  Hint "👉 Start with ```constructor``` to split `isBijection` into injective and surjective goals. From there, use techniques like the previous two levels!"
  constructor
  intro a b c hac hbc
  rw [hac, hbc] --rfl not needed
  intro b
  exist b
  rfl


Conclusion "Bijections are used to make rigorous the idea of two sets having the same \"size\". We'll explore this much more in Cardinality World!"

NewDefinition isBijection
NewTheorem Fun_identity_bij
