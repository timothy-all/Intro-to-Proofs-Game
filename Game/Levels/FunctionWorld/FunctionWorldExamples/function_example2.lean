import Game.Metadata
import Game.Levels.FunctionWorld


World "FunctionWorldExamples"
Level 1

Title "f"

Introduction "Fibers (inverse images of single elements) form equivalence classes.

Check your inventory for the definition of `Rel_fiberrel`."


Statement {u v: Type*} (g: Rel u v) (hg: isFunction g) : isEquivalence (Rel_fiberrel g) := by
  constructor
  intro x
  evaluate hg at x with y hgx hgu
  use y
  intro x1 x2 h
  obtain ⟨y, ⟨hy1,hy2⟩⟩ := h
  use y
  intro x1 x2 x3 ⟨y, ⟨hy1,hy2⟩⟩ ⟨z, ⟨hz1,hz2⟩⟩
  obtain hyz : y = z := Fun_output_equal g hg x2 y z hy2 hz1
  rw [← hyz] at hz2
  use y





Conclusion "."

/-- If `f : Rel u v` is a function and `V : Set v` is a set of elements of `v`, then `Fun_invimage f V` is the set of elements of `u` with the property that `f(u) ∈ V`.

Since we can't directly "plug in" stuff to `f`, the set `Fun_invimage f V` is defined as the set of `u ∈ U` with the property that `f u v` for some `v ∈ V`. Of course, we know there is only one such possible `v`, the one we usually call `f(u)`.-/
DefinitionDoc Rel_fiberrel as "FUN: Rel_fiberrel"
