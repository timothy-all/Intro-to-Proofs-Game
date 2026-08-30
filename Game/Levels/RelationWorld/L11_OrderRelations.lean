import Game.Levels.RelationWorld.L10_OrderRelations

World "RelationWorld"
Level 11

Title "Order Relations"

Introduction " ## **Level 11**

Lastly, let's get some practice with bounds. Let's prove that largest elements are automatically also least upper bounds. Remember that `Supremum` is a fancy word for least upper bound.
"

/--The largest element of a set (if it exists) is its least upper bound.-/
Statement {u : Type*} (R: Rel_on u) (po: isPartialOrder R) (b : u) (B: Set u) (hb: b ∈ B) (lb: isLargest R b B) : isSupremum R b B := by
  Hint "👉 Start with `constructor` to break down the least upper bound conditions."
  constructor
  Hint "It seems that `UpperBounds R B` has appeared - don't panic, this is just the set of upper bounds of B. The new goal simply asks us to prove that `b` is an upper bound of `B`. 👉 Unpack hypotheses using `intro`, then work from there!"
  intro x h
  exact lb.right x h
  intro x hx
  exact hx b hb


Conclusion "That's it for order relations! There are several additional problems in the example world, but we'll continue on to equivalence relations for now."
