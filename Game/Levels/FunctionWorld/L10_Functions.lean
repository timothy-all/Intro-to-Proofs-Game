import Game.Levels.FunctionWorld.L09_Functions


World "FunctionWorld"
Level 10

Title "Functions 10"

Introduction "## **Level 10 : Bijections are invertible**

In the last few levels of Function World, we'll explore the equivalent conditions for functions to be invertible; that is, for `isFunction f.inv` to be true. (Remember that if `R` is a relation, `R.inv` is its inverse.)

Let's start by proving that bijections are invertible."


/--Bijections are invertible.-/
Statement Fun_bij_is_invertible {u v: Type*} (f: Rel u v) (hf: isFunction f) (hbij : isBijection f) : isFunction f.inv := by
  Hint "Start by unpacking what it means for `f` to be a bijection: 👉 ```obtain ⟨finj,fsurj⟩ := hbij```"
  obtain ⟨finj,fsurj⟩ := hbij
  Hint "It's been awhile since we've proven that a relation is a function - 🔍 take a look back at the definition to remind yourself of what needs to be shown!"
  intro b
  obtain ⟨a,ha⟩ := fsurj b
  exist! a
  exact ha
  intro y hy
  obtain eq : a = y
  exact (finj ha hy)
  rw [eq]


Conclusion "The converse is true as well, and that's what we'll show next!"

NewTheorem Fun_bij_is_invertible
