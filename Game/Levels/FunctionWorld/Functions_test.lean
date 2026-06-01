import Game.Levels.FunctionWorld.L05_Functions


World "FunctionWorld"
Level 6

Title "function"

Introduction "Let's work with one-to-one (or injective) functions in Lean. Check your inventory for the new `Fun_isInjective` definition. Remember, we can't really plug an input into a function without using the `evaluate` tactic, so you might be surprised that the definition also has an arbitrary codomain element in it. It functionally works the same as the definition we know though - to see why, try to prove that the compositum of injective functions is injective.

It might be helpful first to `obtain` that `g ∘ f` is a function - we've already proven this, right?"

/-This problem is some kind of nightmare to think through, what helper lemmas can be earlier levels?-/
Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: isInjective g) : isInjective (g ∘ f) := by
  --This is the original level 5 this file was copied from, can ignore
  sorry


/-Maybe this should be a main world level?-/
example {u v: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v u) (hg: isFunction g) (hgf: (g ∘ f) = Rel_id u) : isInjective f := by
  intro a b c fac fbc
  evaluate hg at c with d hdg hdu
  obtain gfad : (g ∘ f) a d := by use c
  obtain gfbd : (g ∘ f) b d := by use c
  rw [hgf] at gfad
  rw [hgf, ← gfad] at gfbd
  exact gfbd.symm



/-Could this helper lemma simplify some levels?-/
example {u v: Type*} (f: Rel u v) (hf: isFunction f) (a : u) (b c : v) : f a b → f a c → b = c := by
  intro fab fac
  evaluate hf at a with d hdf hdu
  obtain bd := hdu b fab
  obtain cd := hdu c fac
  rw [bd]
  exact cd.symm


example {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (a : u) (b : v) (c1 c2 : w) (fab : f a b) (gbc1 : g b c1) (gfac2 : (g ∘ f) a c2) : c1 = c2 := by
  sorry

Conclusion "."
