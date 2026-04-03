import Game.Metadata

World "RelationWorld"
Level 5

Title "Relations 3"

Introduction "Let's get a bit of experience working with a simple explicit relation - the identity relation.
Check out `Rel.id` in your inventory - do you see how this mirrors the definition of our identity relation?
Let's check out that the set of ordered pairs for `Rel.id` is exactly what we expect."

/--Replaces the `set` of the identity relation on `u` with the more concrete set of ordered pairs of the form `(a,a)`.--/
TheoremDoc Rel_id_set as "Rel_id_set"

Statement Rel_id_set {u : Type} : (Rel_id u).set = {(a,a) | a : u} := by
  exact Rel_id_set

Conclusion "."

/- Use these commands to add items to the game's inventory. -/



/-- `Rel.id u` is the identity relation on the universe (type) `u`. --/
DefinitionDoc Rel.id as "Rel.id"
