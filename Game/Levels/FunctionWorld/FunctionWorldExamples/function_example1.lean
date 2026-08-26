import Game.Levels.FunctionWorld.Metadata_FunctionWorld
import Game.Levels.FunctionWorld.Function_docs
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
  exist y
  refine ⟨hgx,hgx⟩
  intro x1 x2 h
  obtain ⟨y, ⟨hy1,hy2⟩⟩ := h
  exist y
  refine ⟨hy2,hy1⟩
  intro x1 x2 x3 ⟨y, ⟨hy1,hy2⟩⟩ ⟨z, ⟨hz1,hz2⟩⟩
  obtain hyz : y = z := Fun_output_equal g hg hy2 hz1
  rw [← hyz] at hz2
  exist y
  refine ⟨hy1,hz2⟩





Conclusion "."


NewDefinition Rel_fiberrel
