import Game.Levels.RelationWorld.L09_OrderRelations

World "RelationWorld"
Level 10

Title "Order Relations"

Introduction "A standard order relation is the 'subset partial order' on a family of sets. If `S` is a subset of `u`, we can write `subsetOrder S` to get this partial order.

To get some practice working with this explicit example, prove that the empty set is the smallest element of a power set using this order.

A weird caveat: The empty set symbol `∅` is bundled with a proof that it's a subset of `S` - don't worry about this too much."

Statement (u : Type*) : isSmallest (subsetOrder u) ∅ := by
  Hint "Start by breaking up our `and` goal using `constructor`."
  constructor
  Hint "The `Set.univ` here is the universe of subsets of `S`, so having the empty set as an element is expected! `apply Set.mem_univ` to close the goal."
  apply Set.mem_univ
  Hint "Can you finish from here?"
  intro h
  intro k
  apply Set.empty_subset

Conclusion "English proof?"

/-- `subsetOrder u` is the subset order relation on a type `u`.-/
DefinitionDoc subsetOrder as "REL: subsetOrder"
