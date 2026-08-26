import Game.Levels.FunctionWorld.FunctionWorldExamples.function_example3


World "FunctionWorldExamples"
Level 4

Title "f"

Introduction "Compositum of injective functions is injective."


/-Original level 5. Simplified a tiny bit with Fun_output_equal, but might just be rough due to using lots of evaluates. They might all be avoidable though, think through it again -/
Statement Fun_comp_inj {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: isInjective g) : isInjective (g ∘ f) := by
  intro a b c gfac gfbc
  obtain gffun := Fun_comp_fun f g hf hg
  evaluate hf at a with y1 hy1f hy1u
  evaluate hf at b with y2 hy2f hy2u
  evaluate hg at y1 with z1 hz1g hz1u
  evaluate hg at y2 with z2 hz2g hz2u
  obtain gfaz1 : (g ∘ f) a z1
  exist y1
  refine ⟨hy1f,hz1g⟩
  obtain gfbz2 : (g ∘ f) b z2
  exist y2
  refine ⟨hy2f,hz2g⟩
  obtain hcz1 : c = z1 := Fun_output_equal (g ∘ f) gffun gfac gfaz1
  obtain hcz2 : c = z2 := Fun_output_equal (g ∘ f) gffun gfbc gfbz2
  rw [← hcz1] at hz1g
  rw [← hcz2] at hz2g
  obtain hy1y2 : y1 = y2 := hgi hz1g hz2g
  rw [hy1y2] at hy1f
  exact hfi hy1f hy2f

NewTheorem Fun_comp_inj





Conclusion "."
