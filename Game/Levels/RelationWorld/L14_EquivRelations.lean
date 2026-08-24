import Game.Levels.RelationWorld.L13_EquivRelations

World "RelationWorld"
Level 14

Title "Equivalence Relations"

Introduction "Recall that the family of equivalence classes of an equivalence relation give a `partition` of the set our relation is on.

Check your inventory for `equivClassFamily`, the notation for the family of equivalence classes.

To get more equivalence relation practice, let's prove the three partition properties. Let's start with showing that the family has no empty elements."



Statement {u : Type*} (R: Rel_on u) (eq: isEquivalence R) : ∅ ∉ equivClassFamily R := by
  Hint "Let's argue by contradiction: `by_contra h`."
  by_contra h
  Hint "`∅ ∈ equivClassFamily R` means ∅ is the equivalence class of something - this is an existentially quantified given. Let's `obtain <a,ha> := h` to say it's the equivalence class of `a`."
  obtain ⟨a,ha⟩ := h
  Hint "But can equivalence classes be empty? Use an equivalence relation property to derive a contradiction!"
  obtain ha2: a ∈ equivClass R a := eq.refl a
  rw [ha] at ha2
  exact ha2

Conclusion "English proof?"

NewTheorem Equiv_class_rep_ind
NewDefinition equivClassFamily
