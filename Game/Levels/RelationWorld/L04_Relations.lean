import Game.Levels.RelationWorld.L03_Relations

World "RelationWorld"
Level 4

Title "Relations 2"

Introduction "  ## **Level 4: The domain of a relation and composite relations**

Composite relations are tricky to work with, but are super important. 🔍 Check out your inventory for how composites work: it's called `REL: ∘`.
Let's get some practice with composites by proving the theorem in this level.
You also have the domain and range for a relation added to your inventory - 🔍 check out their definitions before proceeding."

/-- The domain of a composite relation is a subset of the domain of the inside relation. -/
Statement {u v w : Type} (R: Rel u v) (S: Rel v w) : (S ∘ R).dom ⊆ R.dom := by
  Hint "👉 Start with `intro x h` to grab an arbitrary element of `(S ∘ R).dom`."
  intro x h
  Hint "👉 Use `rw[Rel.dom] at h` to see what it means to be in the domain of `S ∘ R`.
  ### **⌨ Typesetting Tip**
  If you need to write `∘` in the future, it's `\\circ`. "
  rw[Rel.dom] at h
  Hint "👉 Use `obtain ⟨b,hb⟩ := h` to unpack the existentially quantified given."
  obtain ⟨b,hb⟩ := h
  Hint "`hb` is also existentially quantified! 👉 Use `obtain ⟨c,hc⟩ := hb` to unpack it. This is typically how we'll work with composites."
  obtain ⟨c,hc⟩ := hb
  Hint "Can you finish from here? The goal is existentially quantified, even if the quantifier isn't written explicitly."
  exist c --exist
  exact hc.left

Conclusion "You don't need to use `rw[Rel.dom] at h` to see what `Rel.dom` means - it's a definitional swap-out, so you could just immediately move to the next step. Try it!"

NewTheorem Rel_inv_inv
NewDefinition Rel.comp Rel.dom Rel.range
