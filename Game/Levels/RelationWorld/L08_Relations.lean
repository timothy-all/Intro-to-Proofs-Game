import Game.Levels.RelationWorld.L07_Relations

World "RelationWorld"
Level 8

Title "Relations 6"

Introduction "## **Level 8: A transitive example**

Here is a standard transitive example.
### **💡 Pro-tip**
Need to make an ordered pair for a relation? If you know `R` is a relation from `A` to `B` and you know `a ∈ A` and `b ∈ B`, you can assert that `(a,b) ∈ R` by using `obtain h : (a,b) ∈ R.pairs` then proving the resulting goal."

/-- The composition of $R$ with itself is a subset of $R$ if and only if $R$ is transitive.-/
Statement {u : Type} (R: Rel_on u) : (R ∘ R).pairs ⊆ R.pairs ↔ isTransitive R := by
  constructor
  intro h a b c k l
  obtain i : (a,c) ∈ (R ∘ R).pairs
  exist b
  refine ⟨k,l⟩
  exact h i
  intro h x k
  obtain ⟨y,hy⟩ := k
  exact h hy.left hy.right


Conclusion "English proof?"
