import Game.Levels.RelationWorld.L15_EquivRelations
open Set


World "RelationWorld"
Level 16

Title "Equivalence Relations"

Introduction "Finally, we need to show that equivalence classes are pairwise disjoint."


Statement {u : Type*} (R: Rel_on u) (eq: isEquivalence R) : ∀ X Y, X ∈ equivClassFamily R → Y ∈ equivClassFamily R → X ∩ Y ≠ ∅ → X = Y  := by
  Hint "There's a lot to unpack here - `intro X Y hX hY hXY` to name all the assumptions."
  intro X Y hX hY hXY
  Hint "A set being nonempty means that it has an element. Lean calls this fact `nonempty_iff_ne_empty`, so let's `rw [←nonempty_iff_ne_empty] at hXY`."
  rw [←nonempty_iff_ne_empty] at hXY
  Hint "Now use `obtain ⟨a,⟨haX,haY⟩⟩ := h` to grab the element `a`. The embedded angle brackets further deconstruct the intersection into assumptions for each set."
  obtain ⟨a,⟨haX,haY⟩⟩ := hXY
  Hint "Now you're tasked with proving `X = Y` - you can take it from here! There are many ways to do this using what we've done so far."
  obtain ⟨b,hxB⟩ := hX
  obtain ⟨c,hxC⟩ := hY
  rw [←hxB,←hxC]
  rw [←hxB] at haX
  rw [←hxC] at haY
  obtain hac : R a c := eq.symm c a haY
  apply Equiv_class_rep_ind
  exact eq
  exact eq.tran b a c haX hac

Conclusion "English proof?"
