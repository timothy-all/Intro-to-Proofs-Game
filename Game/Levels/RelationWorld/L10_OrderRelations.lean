import Game.Levels.RelationWorld.L09_OrderRelations

World "RelationWorld"
Level 10

Title "Order Relations"

Introduction " ## **Level 10**

A standard order relation is the 'subset partial order' on a family of sets. If `S` is a subset of `u`, we can write `subsetOrder S` to get this partial order.

To get some practice working with this explicit example, prove that the empty set is the smallest element of a power set using this order.

A weird caveat: The empty set symbol `∅` is bundled with a proof that it's a subset of `S` - don't worry about this too much."

open Set

Statement (u : Type*) : isSmallest (subsetOrder u) ∅ := by
  Hint "Start by breaking up our `and` goal using `constructor`."
  constructor
  Hint "The `Set.univ` here is the universe of subsets of `S`, so having the empty set as an element is expected! `apply Set.mem_univ` to close the goal."
  rw[mem_univ_iff_true] -- introd in set world LV12, so they can recall this
  exact trivial
  Hint "Can you finish from here?"
  intro h
  intro k
  rw[subsetOrder]
  intro x hx
  contradiction

Conclusion "English proof?"
