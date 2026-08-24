import Game.Levels.RelationWorld.RelationWorldExamples.relation_example4

World "RelationWorldExamples"
Level 8

Title "Relations"

Introduction "This exercise concerns the union of two relations. Since relations in the Intro Proofs Game use types, not sets, we have to be a bit careful about what this means.

In short, `(Rel_union R S) u v` is true when either `R u v` or `S u v`. Try the problem below, and check your inventory for more information on `Rel_union`."

Statement {u v : Type} (R S: Rel u v) : (Rel_union R S).inv = Rel_union R.inv S.inv  := by
  apply Rel_double_inclusion
  apply double_inclusion
  intro x h
  rcases h with hP | hQ
  left
  exact hP
  right
  exact hQ
  intro x h
  rcases h with hP | hQ
  left
  exact hP
  right
  exact hQ

Conclusion "Proof in English?"

NewDefinition Rel_union
