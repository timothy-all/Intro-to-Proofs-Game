import Game.Levels.RelationWorld.L11_OrderRelations

World "RelationWorld"
Level 12

Title "Equivalence Relations"

Introduction "  ## **Level 12: Equivalence relations**

Let's see how to work with equivalence relations in Lean. Fundamental to equivalence relations are their equivalence classes - 🔍 check your inventory for Lean's terminology for equivalence classes.

The hypothesis `eq` tells us that `R` is an equivalence relation. You can use `eq.refl`, `eq.symm`, `eq.tran` to access the reflexive, symmetric, and transitive properties.

First, let's prove the fundamental fact that equivalence classes are nonempty. More specifically, the equivalence class of `a` contains `a`."


/--Equivalence classes contain their representatives.-/
Statement Equiv_class_has_rep {u : Type*} (R: Rel_on u) (eq: isEquivalence R) (a : u)
 : a ∈ equivClass R a := by
  Hint "The goal is simply to show `R a a`. Which equivalence relation property tells us this?"
  exact eq.refl a


Conclusion "Not too bad! We're going to work toward establishing the relationship between equivalence relations and partitions, so don't rest yet..."

NewDefinition equivClass
