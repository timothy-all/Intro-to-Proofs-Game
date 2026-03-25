import Game.Metadata

World "RelationWorld"
Level 1

Title "Cartesian products"

Introduction "As a tutorial for how to work with Cartesian products of sets in Lean, we will verify what it means for `x` to **not** be in a Cartesian product. We'll assume we have sets `A` and `B` coming from a universe `U`.

The terms `x.fst` and `x.snd` showing up in the goal are how Lean denotes the first and second coordinates of `x`."



Statement (u: Type) (A B: Set u) (x y : u) (h: (x,y) ∉ (A ×ˢ B)) : x ∉ A ∨ y ∉ B := by
  Hint "Let's start by unpacking what it means for `x` to be in a Cartesian product (so we can negate it).
  Try rewriting the set membership using its definition: `rw [mem_prod] at h`."
  rw [mem_prod] at h
  Hint "You should be able to finish it from here!"
  rw [Not_and] at h
  exact h


Conclusion "As a proof in English, our steps here translate to:
Since `x ∉ A × B`, we know that it's not true that the first coordinate of `x` is in `A` and the second coordinate of `x` is in B."

/- Use these commands to add items to the game's inventory. -/

--DefinitionDoc Set.Prod as "×ˢ"

TheoremDoc mem_prod as "mem_prod"

NewTactic intro apply symm Or.inl obtain
NewTheorem mem_prod Not_and
-- NewTheorem Nat.add_comm Nat.add_assoc
NewDefinition Set.Prod
