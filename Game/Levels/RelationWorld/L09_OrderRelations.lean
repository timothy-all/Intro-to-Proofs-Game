import Game.Levels.RelationWorld.L08_Relations

World "RelationWorld"
Level 9

Title "Order Relations"

Introduction "All of the standard order relation definitions have been added to your inventory.

The hypothesis `po` tells us that `R` is a partial order. You can use `po.refl`, `po.anti`, `po.tran` to access the reflexive, anti-symmetric, and transitive properties.

Give the problem below a shot: prove that a smallest element of a set is minimal."

Statement {u : Type*} (R: Rel_on u) (po: isPartialOrder R) (B : Set u) (b: u) (h: isSmallest R b B) : isMinimal R b B := by
  Hint "Minimal elements of `B` have to be in the set, so Lean needs you to first prove that `b ∈ B`. But since `b` is the smallest element of `B`, this is given to use in hypothesis `h`. So first, `obtain ⟨hb,small⟩ := h` to access this."
  obtain ⟨hb,small⟩ := h
  Hint "Now use `constructor` to unpack the conditions for `b` to be minimal, and use `hb` to prove `b ∈ B`. Can you finish from there? You'll eventually need to use that `R` is anti-symmetric!"
  constructor
  exact hb
  intro x xb hx
  obtain smallb := small x xb
  apply po.anti
  refine ⟨hx,smallb⟩



Conclusion "English proof?"

/-- Makes a relation `R` a partial order. If `po: isPartialOrder R`, use `po.refl`, `po.anti`, `po.tran` to access the reflexive, anti-symmetric, and transitive properties, respectively. -/
DefinitionDoc isPartialOrder as "REL: isPartialOrder"

/-- If `R` is a relation on `u`, `isMinimal R b` means that `b` is a minimal element of `u`.

If we want to specify that `b` is a minimal element of a subset `B` of `u`, write `isMinimal R b B`. -/
DefinitionDoc isMinimal as "REL: isMinimal"

/-- If `R` is a relation on `u`, `isMaximal R b` means that `b` is a maximal element of `u`.

If we want to specify that `b` is a maximal element of a subset `B` of `u`, write `isMaximal R b B`. -/
DefinitionDoc isMaximal as "REL: isMaximal"

/-- If `R` is a relation on `u`, `isSmallest R b` means that `b` is the smallest element of `u`.

If we want to specify that `b` is the smallest element of a subset `B` of `u`, write `isSmallest R b B`. -/
DefinitionDoc isSmallest as "REL: isSmallest"

/-- If `R` is a relation on `u`, `isLargest R b` means that `b` is the largest element of `u`.

If we want to specify that `b` is the largest element of a subset `B` of `u`, write `isLargest R b B`. -/
DefinitionDoc isLargest as "REL: isLargest"

/-- If `R` is a relation on `u`, `isLowerBound R l B` means that `l` is a lower bound for the subset `B` of `u`. -/
DefinitionDoc isLowerBound as "REL: isLowerBound"

/-- If `R` is a relation on `u`, `isUpperBound R s B` means that `u` is an upper bound for the subset `B` of `u`. -/
DefinitionDoc isUpperBound as "REL: isUpperBound"

/-- If `R` is a relation on `u`, `isInfimum R l B` means that `l` is the greatest lower bound for the subset `B` of `u`. -/
DefinitionDoc isInfimum as "REL: isInfimum"

/-- If `R` is a relation on `u`, `isSupremum R s B` means that `s` is the least upper bound for the subset `B` of `u`. -/
DefinitionDoc isSupremum as "REL: isSupremum"
