import Game.Levels.PfWorld.L02_pf

World "PfWorld"
Level 3

Title "Contrapose!"

Introduction "
# **Level 3: Contraposition**
Here's a classic example of a statement we should approach via contraposition.
"

/-- If $x$ is an integer such that $x^2$ is not even, then $x$ isn't even.-/
Statement (x : ℤ) : ¬ isEven (x ^ 2) → ¬ isEven x := by
  contrapose
  Hint "Notice that our goal is now `⊢ ¬¬isEven x → ¬¬isEven (x ^ 2). After getting rid of the double negations, we can approach this directly. See if you can't complete this level on your own from here."
  rw[Not_not,Not_not]
  intro h
  obtain ⟨k,hk⟩ := h
  exist 2 * k ^ 2
  rw[hk]
  simplify

Conclusion ""
