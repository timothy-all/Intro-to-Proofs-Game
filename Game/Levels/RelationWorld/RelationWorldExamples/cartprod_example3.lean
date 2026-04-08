import Game.Levels.RelationWorld.RelationWorldExamples.cartprod_example2

World "RelationWorldExamples"
Level 3

Title "Cartesian products"

Introduction "Cartesian products: What does it mean for `A × B` and `C × D` to be disjoint?

In the statement of the theorem below, we're assuming `A` and `C` come from the same universe; similar for `B` and `D`. Of course, if either fails, the conclusion is automatically true."


Statement (u v: Type) (A C: Set u) (B D: Set v) (h: ((A ×ˢ B) ∩ (C ×ˢ D) = ∅)): (A ∩ C = ∅) ∨ (B ∩ D = ∅) := by
  by_contra! F
  rw[Set.nonempty_def,Set.nonempty_def] at F
  rcases F with ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  obtain hAB : (x,y) ∈ A ×ˢ B := And.intro hx.left hy.left
  obtain hCD : (x,y) ∈ C ×ˢ D := And.intro hx.right hy.right
  obtain F : (x,y) ∈ (A ×ˢ B) ∩ (C ×ˢ D) := And.intro hAB hCD
  rw[h] at F
  contradiction

Conclusion "Proof in English?"

/- Use these commands to add items to the game's inventory. -/

--DefinitionDoc Set.Prod as "×ˢ"

TheoremDoc mem_prod as "mem_prod"
TheoremDoc Set.Subset.antisymm as "double_inclusion"

--TheoremDoc Set.eq_of_subset_of_subset as "double_inclusion"

--NewTactic intro apply symm Or.inl obtain
NewTheorem mem_prod Set.Subset.antisymm
-- NewTheorem Nat.add_comm Nat.add_assoc
NewDefinition Set.Prod

/- Original proof; avoid using `have`
theorem test (u v: Type) (A C: Set u) (B D: Set v) (h: ((A ×ˢ B) ∩ (C ×ˢ D) = ∅)): (A ∩ C = ∅) ∨ (B ∩ D = ∅) := by
  rw[or_iff_not_imp_left]
  intro k
  rw [←ne_eq,←Set.nonempty_iff_ne_empty,Set.nonempty_def] at k
  obtain ⟨x,kx⟩ := k
  rw [mem_inter] at kx
  obtain ⟨ka, kb⟩ := kx
  by_contra l
  rw [←ne_eq, ← Set.nonempty_iff_ne_empty, Set.nonempty_def] at l
  obtain ⟨y,ly⟩ := l
  rw [mem_inter] at ly
  obtain ⟨la,lb⟩ := ly
  have prod1 : (x,y) ∈ A ×ˢ B := by
    rw [mem_prod]
    constructor
    exact ka
    exact la
  have prod2: (x,y) ∈ C ×ˢ D := by
    rw [mem_prod]
    constructor
    exact kb
    exact lb
  have both_prod : (x,y) ∈ (A ×ˢ B) ∩ (C ×ˢ D) := by
    rw [mem_inter]
    constructor
    exact prod1
    exact prod2
  rw [h, Set.mem_empty_iff_false] at both_prod
  exact both_prod
-/
