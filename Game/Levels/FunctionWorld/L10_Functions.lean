import Game.Levels.FunctionWorld.L09_Functions


World "FunctionWorld"
Level 10

Title "function"

Introduction "In the last few levels, we'll explore the equivalent conditions for functions to be invertible; that is, for `isFunction f.inv` to be true. (Remember that if `R` is a relation, `R.inv` is its inverse.)

Let's start with bijections being invertible."

Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) : isBijection f → isFunction f.inv  := by
  intro h
  obtain ⟨finj,fsurj⟩ := h
  intro b
  obtain ⟨a,ha⟩ := fsurj b
  use! a
  refine ⟨ha,?_⟩
  intro y hy
  exact (finj a y b ha hy).symm


Conclusion "."
