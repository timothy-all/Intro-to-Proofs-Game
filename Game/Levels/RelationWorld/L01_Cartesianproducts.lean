import Game.Levels.SetWorld
import Game.Levels.RelationWorld.Metadata_RelationWorld

World "RelationWorld"
Level 1

Title "Cartesian products"

Introduction "As a tutorial for how to work with Cartesian products of sets in Lean, we will verify what it means for `x` to **not** be in a Cartesian product. We'll assume we have sets `A` and `B` coming from universes `u` and `v`.

Note: When discussing relations in Lean, we won't actually use Cartesian products of **sets**, but instead Cartesian products of **types**. Despite this, getting some practice with Cartesian products of sets now will help you write proofs involving Cartesian products of sets (and relations!) outside of Lean.

The terms `x.fst` and `x.snd` showing up in the goal are how Lean denotes the first and second coordinates of `x`. We will often use the simpler `x.1` and `x.2` to access the coordinates."

/--
doc
-/
TheoremDoc not_mem_prod as "REL: not_mem_prod"

Statement not_mem_prod (u v: Type) (A: Set u) (B: Set v) (x : u) (y: v) (h: (x,y) ∉ (A ×ˢ B)) : x ∉ A ∨ y ∉ B := by
  Hint "Let's start by unpacking what it means for `x` to be in a Cartesian product (so we can negate it).
  Try rewriting the set membership using its definition: `rw [mem_prod] at h`."
  rw [mem_prod] at h
  Hint "Lean treats `(x,y).1` as the same thing as `x` - no need to rewrite it further to use it just like `x`, though in proofs written by hand we certainly would write just `x`. (This same notation works with Cartesian products of types later!)
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
TheoremDoc mem_prod as "REL: mem_prod"

NewTheorem mem_prod
-- NewTheorem Nat.add_comm Nat.add_assoc
