import Game.Levels.PfWorld.L09_pf

World "PfWorld"
Level 10

Title "Disjunctive hypotheses"

Introduction "
# **Level 10: Disjunctive hypotheses**
"

--Or statement

Statement (u : Type*) (A B C : Set u) : A ∪ C = B ∪ C → (A \ B ∪ B \ A) ⊆ C := by
  intro h x hx
  obtain hxa | hxb := hx -- here
  obtain hxAC : x ∈ A ∪ C
  left
  exact hxa.left
  rw[h] at hxAC
  obtain hxB | hxC := hxAC
  obtain hxB' := hxa.right
  contradiction
  exact hxC
  obtain hxBC : x ∈ B ∪ C
  left
  exact hxb.left
  rw[← h] at hxBC
  obtain hxA | hxC := hxBC
  obtain hxA' := hxb.right
  contradiction
  exact hxC


Conclusion ""
