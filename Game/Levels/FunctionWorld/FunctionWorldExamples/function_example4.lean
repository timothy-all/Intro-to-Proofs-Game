import Game.Levels.FunctionWorld.FunctionWorldExamples.function_example3


World "FunctionWorldExamples"
Level 4

Title "f"

Introduction "Compositum of injective functions is injective."


/-Original level 5. Simplified a tiny bit with Fun_output_equal, but might just be rough due to using lots of evaluates -/
Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: isInjective g) : isInjective (g ∘ f) := by
  intro a b c gfac gfbc
  obtain gffun := Fun_comp_fun f g hf hg
  evaluate hf at a with y1 hy1f hy1u
  evaluate hf at b with y2 hy2f hy2u
  evaluate hg at y1 with z1 hz1f hz1u
  evaluate hg at y2 with z2 hz2f hz2u
  obtain gfaz1 : (g ∘ f) a z1 := by
    use y1
  obtain gfbz2 : (g ∘ f) b z2 := by
    use y2
  obtain hcz1 : c = z1 := Fun_output_equal (g ∘ f) gffun a c z1 gfac gfaz1
  obtain hcz2 : c = z2 := Fun_output_equal (g ∘ f) gffun b c z2 gfbc gfbz2
  rw [← hcz1] at hz1f
  rw [← hcz2] at hz2f
  obtain hy1y2 : y1 = y2 := hgi y1 y2 c hz1f hz2f
  rw [hy1y2] at hy1f
  exact hfi a b y2 hy1f hy2f





Conclusion "."
