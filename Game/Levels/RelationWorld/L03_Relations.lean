import Game.Levels.RelationWorld.L02_Cartesianproducts

World "RelationWorld"
Level 3

Title "Relations 1"

Introduction "Relations in the Intro Proofs Game are defined with the ''aRb'' notation in mind, but this ''infix'' notation isn't used. If `R` is a relation from A to B, we'll write `R a b` to say that a relates to b.
Given a relation `R`, we can access the corresponding set of ordered pairs by using `R.set`. To be clear, if `R a b` is true, then we can't just write `(a,b) ∈ R` - we will have to write `(a,b) ∈ R.set`.
To get used to this, let's prove something very basic - the inverse of a relation's inverse is the original relation.
Check your inventory for the exact definition of `Rel.inv` so you can use it in your proof."

/-- The inverse of the inverse of a relation is itself. --/
TheoremDoc Rel_inv_inv as "REL: Rel_inv_inv"

/-- Swaps out relation equality with the underlying set equality. --/
TheoremDoc Rel_double_inclusion as "REL: Rel_double_inclusion"

Statement Rel_inv_inv {u v : Type} (R: Rel u v) : (R.inv).inv = R := by
  Hint "Lean views this as an equality of `functions`. To replace relation equality with the more familiar double inclusion set proofs from class, we can `apply Rel_double_inclusion`."
  apply Rel_double_inclusion
  Hint "Now do a double inclusion proof from here! Start with `apply double_inclusion` then `intros x h`."
  apply double_inclusion
  intros x h
  Hint "Lean knows that the inverse just swaps the coordinates, so `h` is already definitionally equal to the goal! In English, you'd want to mention that the coordinates swap twice."
  exact h
  intro x
  intro h
  exact h


Conclusion "Relation facts can also be proven by using their core definition - as Lean functions. If you want to also try this, `funext x y` will unpack the equality in this way.
We'll work with functions much more explicitly in Function World."

/- Use these commands to add items to the game's inventory. -/

/-- `R.inv` is the inverse of the relation `R`. --/
DefinitionDoc Rel.inv as "REL: Rel.inv"
