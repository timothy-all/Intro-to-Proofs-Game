import Game.Levels.FunctionWorld.L04_Functions


World "FunctionWorld"
Level 5

Title "function"

Introduction "Let's work with one-to-one (or injective) functions in Lean. Check your inventory for the new `Fun_isInjective` definition. Remember, we can't really plug an input into a function without using the `evaluate` tactic, so you might be surprised that the definition also has an arbitrary codomain element in it. It functionally works the same as the definition we know though - to see why, try to prove that the compositum of injective functions is injective.

It might be helpful first to `obtain` that `g ∘ f` is a function - we've already proven this, right?"


Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: Fun_isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: Fun_isInjective g) : Fun_isInjective (g ∘ f) := by
  intro a b c h
  obtain gffun := Fun_comp_fun f g hf hg
  evaluate hf at a with y1 hy1
  evaluate hf at b with y2 hy2
  evaluate hg at y1 with z1 hz1
  evaluate hg at y2 with z2 hz2
  --This sets up y1 = f(a) and y2 = f(b), so we have g(y1) = g(y2); need to get Lean to see this by unpacking function stuff & relating them to c
  --This is very painful, or I'm missing something large
  obtain hgy1c : g y1 c := by
    obtain gcfaz1 : (g ∘ f) a z1 := by
      use y1
      constructor
      exact hy1.left
      exact hz1.left


    sorry
  sorry




Conclusion "."
