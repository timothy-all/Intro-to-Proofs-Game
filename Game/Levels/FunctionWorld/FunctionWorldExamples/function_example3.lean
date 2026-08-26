import Game.Levels.FunctionWorld.FunctionWorldExamples.function_example2


World "FunctionWorldExamples"
Level 3

Title "f"

Introduction "A function `f` with a right inverse is onto."


Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v u) (hg: isFunction g) (hfg: (f ∘ g) = Rel_id v) : isSurjective f := by
  intro b
  evaluate hg at b with a hag hau
  exist a
  evaluate hf at a with c hcg hcu
  obtain fgbc : (f ∘ g) b c
  exist a
  refine ⟨hag,hcg⟩
  rw [hfg] at fgbc
  rw [←fgbc] at hcg
  exact hcg





Conclusion "."
