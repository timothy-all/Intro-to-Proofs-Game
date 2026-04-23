import Game.Levels.RelationWorld.L10_OrderRelations

World "RelationWorld"
Level 11

Title "Order Relations"

Introduction "Lastly, let's get some practice with bounds. Let's prove that largest elements are automatically also least upper bounds. Remember that `Supremum` is the fancy math word for least upper bound."

Statement {u : Type*} (R: Rel_on u) (po: isPartialOrder R) (b : u) (B: Set u) (hb: b ∈ B) (lb: isLargest R b B) : isSupremum R b B := by
  Hint "Start with `constructor` to break down the least upper bound conditions."
  constructor
  Hint "`UpperBounds R B` is the set of upper bounds of B, so the new goal asks us to prove `b` is an upper bound of `B`. Unpack hypotheses using `intro`, then work from there!"
  intro x h
  exact lb.right x h
  intro x hx
  exact hx b hb


Conclusion "English proof?"

/-- If `S: Set u`, `subsetOrder S` is the subset order relation on `S`.-/
DefinitionDoc subsetOrder as "REL: subsetOrder"
