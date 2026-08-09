import Game.Levels.FunctionWorld.L10_Functions


World "FunctionWorld"
Level 11

Title "function"

Introduction "This is the converse of the previous level: invertible functions are bijections."

/-- Invertible functions are bijections. -/
TheoremDoc Fun_invertible_is_bij as "FUN: Fun_invertible_is_bij"

Statement Fun_invertible_is_bij {u v: Type*} (f: Rel u v) (hf: isFunction f) : isFunction f.inv → isBijection f := by
  intro finv
  constructor
  intro a b c fac fbc
  --Recall that f a c is definitionally equal to f.inv c a
  exact Fun_output_equal f.inv finv c a b fac fbc
  intro b
  evaluate finv at b with a hafinv hau
  use a
  exact hafinv


Conclusion "."
