import Game.Levels.FunctionWorld.L10_Functions


World "FunctionWorld"
Level 11

Title "function"

Introduction "This is the converse of the previous level: invertible functions are bijections."



Statement Fun_invertible_is_bij {u v: Type*} (f: Rel u v) (hf: isFunction f) : isFunction f.inv → isBijection f := by
  intro finv
  constructor
  intro a b c fac fbc
  --Recall that f a c is definitionally equal to f.inv c a
  exact Fun_output_equal f.inv finv fac fbc
  intro b
  evaluate finv at b with a hafinv hau
  exist a
  exact hafinv


Conclusion "."

NewTheorem Fun_invertible_is_bij
