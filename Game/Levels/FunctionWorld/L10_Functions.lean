import Game.Levels.FunctionWorld.L09_Functions


World "FunctionWorld"
Level 10

Title "function"

Introduction "In the last few levels, we'll explore the equivalent conditions for functions to be invertible; that is, for `isFunction f.inv` to be true. (Remember that if `R` is a relation, `R.inv` is its inverse.)

Let's start with bijections being invertible."



Statement Fun_bij_is_invertible {u v: Type*} (f: Rel u v) (hf: isFunction f) : isBijection f → isFunction f.inv  := by
  intro h
  obtain ⟨finj,fsurj⟩ := h
  intro b
  obtain ⟨a,ha⟩ := fsurj b
  exist! a
  exact ha
  intro y hy
  obtain eq : a = y
  exact (finj ha hy)
  rw [eq]


Conclusion "."

NewTheorem Fun_bij_is_invertible
