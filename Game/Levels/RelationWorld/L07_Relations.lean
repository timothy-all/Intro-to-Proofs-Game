import Game.Levels.RelationWorld.L06_Relations

World "RelationWorld"
Level 7

Title "Relations 5"

Introduction " ## **Level 7: A symmetric example**

Here is a standard symmetric example.
**💡 Pro-tip**
Remember, you can `apply h` to move *backwards* with a goal; it's like saying \"it suffices to show\" in English. You can also `apply h at k` use what we know about `h` to deduce something from `k`; it's like saying \"Since we know `k`, `h` tells us...\"."

/-- $R ⊆ R^{-1}$ if and only if $R$ is symmetric. -/
Statement {u : Type} (R: Rel_on u) : R.inv.pairs ⊆ R.pairs ↔ isSymmetric R := by
  constructor
  intro h x a k
  obtain i : (a,x) ∈ R.inv.pairs
  exact k
  apply h at i
  exact i
  intro h x k
  apply h at k
  exact k


Conclusion "Lastly, let's look at a transitive example."
