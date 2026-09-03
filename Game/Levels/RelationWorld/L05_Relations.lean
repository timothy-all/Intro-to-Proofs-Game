import Game.Levels.RelationWorld.L04_Relations

World "RelationWorld"
Level 5

Title "Relations 3"

Introduction " ## **Level 5: The identity relation**

Let's get a bit of experience working with a simple explicit relation - the identity relation.
🔍 Check out `Rel.id` in your inventory - do you see how this mirrors the definition of our identity relation?
🔍 Note also the new definition for `Rel_on u` - this is simply a shorthand for `Rel u u`, just as we use in class.
Let's check out that the set of ordered pairs for `Rel.id` is exactly what we expect."


/-- The set of pairs for the identity relation is simply the set of pairs $(a,a)$.-/
Statement Rel_id_pairs {u : Type} : (Rel_id u).pairs = {(a,a) | a : u} := by
  Hint "👉 Let's do a double inclusion proof - ```apply Double_inclusion```"
  apply Double_inclusion
  Hint "We'll walk through the first inclusion: it's a bit tricky! 👉 Grab an arbitrary element of `Rel.pairs (Rel_id u)` - ```intro x hx```."
  intro x hx
  Hint "What does `hx` even mean? 👉 Let's unpack it with ```rw[Rel.pairs] at hx```"
  rw[Rel.pairs] at hx
  Hint "Now can see that `hx` means that the coordinates of `x` relate under the identity relation; that is, `x.1 = x.2`. In that case, we can provide either `x.1` or `x.2` to satisfy our existence goal. 👉 Let's go with ```exist x.1```"
  exist x.1
  Hint "## **❯ The `nth_rw` tactic**
  The tactic `nth_rw` does a *targeted rewrite* at a specific position in an expression. Our goal here is to prove that `(x.1,x.1) = x`. But `(x.1,x.2) = x` and we know `x.1 = x.2`, so a simple `rw [hx]` *should* work. But Lean gets overexcited and replaces *all* occurrences of `x.1` with `x.2`! 👉 To just replace the second, try ```nth_rw 2 [hx]```
  "
  nth_rw 2 [hx]
  Hint "Just like `rw`, `nth_rw` automatically applied `rfl` to close the goal once it was true by equality. Now give the reverse inclusion a shot yourself!"
  intro x hx
  obtain ⟨a,ha⟩ := hx
  rw [←ha]
  rfl

Conclusion "The identity relation is very import when talking about inverses of functions, something we'll see much later."

/- Use these commands to add items to the game's inventory. -/

NewDefinition Rel_on Rel_id
NewTheorem Rel_id_pairs
NewTactic nth_rw
