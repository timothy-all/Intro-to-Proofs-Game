import Game.Levels.RelationWorld.RelationWorldExamples.relation_example5

World "RelationWorldExamples"
Level 9

Title "Order Relations"

Introduction "Let's prove a theorem about how least upper bounds of subsets compare when the subsets are nested."

Statement {u : Type*} (R : Rel_on u) (B1 B2: Set u) (x1 x2: u) (h1: isSupremum R x1 B1) (h2: isSupremum R x2 B2) (h: B1 ⊆ B2) : R x1 x2 := by
  obtain ⟨h1ub, h1lub⟩:= h1
  obtain ⟨h2ub, h2lub⟩:= h2
  obtain x2ubB1 : isUpperBound R x2 B1
  intro x hx
  obtain hxb2 := h hx
  exact h2ub x hxb2
  exact h1lub x2 x2ubB1

Conclusion "Proof in English?"
