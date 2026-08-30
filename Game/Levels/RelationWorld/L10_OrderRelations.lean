import Game.Levels.RelationWorld.L09_OrderRelations

World "RelationWorld"
Level 10

Title "Order Relations"

Introduction " ## **Level 10: The subset partial order**

A standard order relation is the 'subset partial order' on a family of sets. If `u` is a set, then `subsetOrder u` is this partial order. 🔍 Check your inventory for a bit more detail.

To get some practice working with this explicit example, prove that the empty set is the smallest element of a power set using this order.

A weird caveat: The empty set symbol `∅` is bundled with a proof that it's a subset of `S` - don't worry about this too much."

open Set

/-- The smallest element of the subset partial order on any set is ∅.-/
Statement (u : Type*) : isSmallest (subsetOrder u) ∅ := by
  Hint "👉 Start by breaking up our `and` goal using `constructor`."
  constructor
  Hint "It might be helpful to look back at some results from `SetWorld` - anything should be an element of the universe, right?"
  rw[mem_univ_iff_true] -- introd in set world LV12, so they can recall this
  exact trivial
  Hint "Can you finish from here?"
  intro h
  intro k
  --rw[subsetOrder]
  intro x hx
  contradiction

Conclusion "Remember, again, smallest elements don't have to exist. For this specific partial order, they always do!"

NewDefinition subsetOrder
