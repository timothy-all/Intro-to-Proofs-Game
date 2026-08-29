import Game.Levels.FunctionWorld.FunctionWorldExamples.function_example4


World "FunctionWorldExamples"
Level 5

Title "f"

Introduction "For onto functions, `image` undoes `invimage`."


Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isSurjective f) (V: Set v) : image f (invimage f V) = V := by
  apply Double_inclusion
  intro b hb
  obtain ⟨a, ⟨⟨c,⟨hc,fac⟩⟩,fab⟩⟩ := hb
  obtain hbc : b = c := Fun_output_equal f hf fab fac
  rw[hbc]
  exact hc
  intro b hb
  obtain ⟨a,ha⟩ := hfi b
  exist a
  refine ⟨?_,ha⟩
  exist b
  refine ⟨hb,ha⟩





Conclusion "."
