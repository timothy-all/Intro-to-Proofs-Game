import Game.Metadata

World "RelationWorld"
Level 5

Title "Relations 3"

Introduction "Let's get a bit of experience working with a simple explicit relation - the identity relation.
Check out `Rel.id` in your inventory - do you see how this mirrors the definition of our identity relation?
Let's check out that the set of ordered pairs for `Rel.id` is exactly what we expect."

Statement {u : Type} : (Rel_id u).set = {(a,a) | a : u} := by
  apply double_inclusion
  intros x hx
  unfold Rel.set at hx
  simp at hx --Unsure how to not use simp here
  use x.1
  nth_rw 2 [hx]
  intros x hx
  obtain ⟨a,ha⟩ := hx
  rw [←ha]
  rfl

Conclusion "."

/- Use these commands to add items to the game's inventory. -/

/-- `Rel.id u` is the identity relation on the universe (type) `u`. --/
DefinitionDoc Rel.id as "Rel.id"
