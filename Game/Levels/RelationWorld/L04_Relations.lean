import Game.Levels.RelationWorld.L03_Relations

World "RelationWorld"
Level 4

Title "Relations 2"

Introduction "  ## **Level 4**

Composite relations are tricky to work with, but are super important.
Let's get some practice with composites by proving the theorem in this level.
You also have the domain and range for a relation added to your inventory - check out their definitions before proceeding."

Statement {u v w : Type} (R: Rel u v) (S: Rel v w) : (S ∘ R).dom ⊆ R.dom := by
  Hint "Start with `intro x h` to grab an arbitrary element of `(S ∘ R).dom`."
  intro x h
  Hint "Use `rw[Rel.dom] at h` to see what it means to be in the domain of `S ∘ R`. "
  rw[Rel.dom] at h
  Hint "Use `obtain ⟨b,hb⟩ := h` to unpack the existentially quantified given."
  obtain ⟨b,hb⟩ := h
  Hint "`hb` is also existentially quantified! Use `obtain <c,hc> := hb` to unpack it. This is typically how we'll work with composites."
  obtain ⟨c,hc⟩ := hb
  Hint "Can you finish from here? The goal is existentially quantified, even if the quantifier isn't written explicitly."
  exist c --exist
  exact hc.left

Conclusion "You don't need to use unfold first to unpack the existential quantifier in `(S ∘ R).dom`; we could grab it directly too. The English analog of this is how we don't write the existential quantifier in ''indexed'' set builder notation."

NewTheorem Rel_inv_inv
NewDefinition Rel.dom Rel.range
