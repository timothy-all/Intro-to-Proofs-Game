import Game.Metadata

World "RelationWorld"
Level 1

Title "Cartesian products"

Introduction "As a tutorial for how to work with Cartesian products of sets in Lean, we will verify what it means for `x` to **not** be in a Cartesian product. We'll assume we have sets `A` and `B` coming from a universe `U`.

The terms `x.fst` and `x.snd` showing up in the goal are how Lean denotes the first and second coordinates of `x`."

/--
doc
-/
TheoremDoc not_mem_prod as "not_mem_prod"

Statement not_mem_prod (u v: Type) (A: Set u) (B: Set v) (x : u) (y: v) (h: (x,y) ∉ (A ×ˢ B)) : x ∉ A ∨ y ∉ B := by
  Hint "Let's start by unpacking what it means for `x` to be in a Cartesian product (so we can negate it).
  Try rewriting the set membership using its definition: `rw [mem_prod] at h`."
  rw [mem_prod] at h
  Hint "Lean treats `(x,y).1` as the same thing as `x` - no need to rewrite it further to use it just like `x`, though in proofs written by hand we certainly would write just `x`.
  You should be able to finish it from here!"
  rw [Not_and] at h
  exact h


Conclusion "As a proof in English, our steps here translate to:
Since `x ∉ A × B`, we know that it's not true that the first coordinate of `x` is in `A` and the second coordinate of `x` is in B.
unfinished"

/- Use these commands to add items to the game's inventory. -/

--DefinitionDoc Set.Prod as "×ˢ"

/--
Doc
-/
TheoremDoc mem_prod as "mem_prod"

NewTheorem mem_prod
-- NewTheorem Nat.add_comm Nat.add_assoc
