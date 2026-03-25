import Game.Metadata

World "TestWorld"
Level 1

Title "Test"

Introduction "
"

theorem test1 {u : Type} (A B C : Set u) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hxA
  exact h2 (h1 hxA)

theorem test2 {u : Type} (A B : Set u) (p : u → Prop) (q : u → Prop) (h : ∀ x : u, p x → q x) : {x | p x} ⊆ {x | q x} := by
  intro a ha
  exact h a ha

theorem test4 {u : Type} (A B : Set u) : (A ∪ B)ᶜ = (Aᶜ ∩ Bᶜ) := by
  ext
  rw[Set.mem_compl_iff]
  rw[Set.mem_union]
  rw[Not_or]
  rw[Set.mem_inter_iff]
  rw[Set.mem_compl_iff,Set.mem_compl_iff]

Conclusion "
"
