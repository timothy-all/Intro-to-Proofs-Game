import Game.Levels.FunctionWorld.FunctionWorldExamples.function_example5


World "FunctionWorldExamples"
Level 6

Title "f"

Introduction "A function with a left inverse is one-to-one."


Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v u) (hg: isFunction g) (hgf: (g ∘ f) = Rel_id u) : isInjective f := by
  intro a b c fac fbc
  evaluate hg at c with d hdg hdu
  obtain gfad : (g ∘ f) a d
  exist c
  refine ⟨fac,hdg⟩
  obtain gfbd : (g ∘ f) b d
  exist c
  refine ⟨fbc,hdg⟩
  rw [hgf] at gfad
  rw [hgf, ← gfad] at gfbd
  exact gfbd.symm





Conclusion "."
