import Game.Levels.FunctionWorld.L05_Functions


World "FunctionWorld"
Level 6

Title "function"

Introduction "Let's work toward using bijections and inverses in Lean. We'll start with one-to-one functions: check your inventory for the new `isInjective` definition. Remember, we can't really plug an input into a function without using the `evaluate` tactic, so you might be surprised that the definition also has an arbitrary codomain element in it. It functionally works the same as the definition we know though!"

Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (hgf: isInjective (g ∘ f)) : isInjective f := by
  intro a1 a2 b fa1b fa2b
  evaluate hg at b with c hcg hcu
  obtain gfa1c : (g ∘ f) a1 c := by use b
  obtain gfa2c : (g ∘ f) a2 c := by use b
  exact hgf a1 a2 c gfa1c gfa2c


Conclusion "."


/-- If `f : Rel u v` is a function, `isInjective f` means that `f` is one-to-one. -/
DefinitionDoc isInjective as "FUN: isInjective"
