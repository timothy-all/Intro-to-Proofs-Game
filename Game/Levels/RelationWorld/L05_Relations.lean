import Game.Levels.RelationWorld.L04_Relations

World "RelationWorld"
Level 5

Title "Relations 3"

Introduction " ## **Level 5**

Let's get a bit of experience working with a simple explicit relation - the identity relation.
Check out `Rel.id` in your inventory - do you see how this mirrors the definition of our identity relation?
Note also the new definition for `Rel_on u` - this is simply a shorthand for `Rel u u`, just as we use in class.
Let's check out that the set of ordered pairs for `Rel.id` is exactly what we expect."



Statement Rel_id_set {u : Type} : (Rel_id u).set = {(a,a) | a : u} := by
  apply double_inclusion
  intro x hx
  rw[Rel.set] at hx
  exist x.1
  nth_rw 2 [hx] -- intro nth-rewrite
  intro x hx
  obtain ⟨a,ha⟩ := hx
  rw [←ha]
  rfl

Conclusion "."

/- Use these commands to add items to the game's inventory. -/

NewDefinition Rel_on Rel_id
