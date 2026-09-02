import Game.Levels.FunctionWorld.L10_Functions


World "FunctionWorld"
Level 11

Title "Functions 11"

Introduction "## **Level 11 : Invertible functions are bijections**

This is the converse of the previous level: invertible functions are bijections."


/--Invertible functions are bijections. -/
Statement Fun_invertible_is_bij {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfinv: isFunction f.inv) : isBijection f := by
  Hint "Start with 👉 `constructor` to break the goal into injective and surjective parts. The injective part will be first, so grab the large number of terms that we need to manipulate for it: 👉 `intro a b c fac fbc`."
  constructor
  intro a b c fac fbc
  Hint "Lean views `f.inv c a` as literally the same thing as `f a c`. Can you see how to use that `f` is a function to close the goal? Remember, we proved 🔍 `Fun_output_equal` many levels ago..."
  exact Fun_output_equal f.inv hfinv fac fbc
  Hint "For the surjective part, here's one major hint: because `f.inv` is a function you can *plug stuff into it*. You may even say we can `evaluate` it..."
  intro b
  evaluate hfinv at b with a hafinv hau
  exist a
  exact hafinv


Conclusion "With the last two levels, we know that a function is invertible if and only if it's a bijection. The last thing we'll look at in the main Function World levels is the relationship between invertible functions and the identity function."

NewTheorem Fun_invertible_is_bij
