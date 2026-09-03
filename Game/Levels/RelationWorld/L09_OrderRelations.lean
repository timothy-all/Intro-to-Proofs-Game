import Game.Levels.RelationWorld.L08_Relations

World "RelationWorld"
Level 9

Title "Order Relations"

Introduction " ## **Level 9: Partial orders**

🔍 All of the standard order relation definitions (minimal, maximal, etc) have been added to your inventory - check them out!

The hypothesis `po` tells us that `R` is a partial order. You can use `po.refl`, `po.anti`, `po.tran` to access the reflexive, anti-symmetric, and transitive properties.

Give the problem below a shot."

/-- The smallest element of a set (if it exists) is a minimal element.-/
Statement {u : Type*} (R: Rel_on u) (po: isPartialOrder R) (B : Set u) (b: u) (h: isSmallest R b B) : isMinimal R b B := by
  Hint "Minimal elements of `B` have to be in the set, so Lean needs you to first prove that `b ∈ B`. But since `b` is the smallest element of `B`, this is given to use in hypothesis `h`. 👉 So first, ```obtain ⟨hb,small⟩ := h``` to access this."
  obtain ⟨hb,small⟩ := h
  Hint "👉 Now use ```constructor``` to unpack the conditions for `b` to be minimal, and use `hb` to prove `b ∈ B`.
  Can you finish from there? You'll eventually need to use that `R` is anti-symmetric! Remember that this fact is called `po.anti` here."
  constructor
  exact hb
  intro x xb hx
  obtain smallb := small x xb
  apply po.anti
  refine ⟨hx,smallb⟩

NewDefinition isPartialOrder isMinimal isMaximal isSmallest isLargest isLowerBound isUpperBound isInfimum isSupremum

Conclusion "Keep in mind that smallest elements don't have to exist - think of ℤ with the partial order ≤, for instance."
