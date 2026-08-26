import Game.Levels.FunctionWorld.L12_Functions


World "FunctionWorld"
Level 13

Title "function"

Introduction "This is the converse of the last level, a fitting boss for FunctionWorld!"

/-Can this be simplified using previous levels beyond Fun_output_equal and Fun_comp_fun?-/
Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) :  isFunction f.inv → (f ∘ f.inv) = Rel_id v ∧ (f.inv ∘ f) = Rel_id u  := by
  intro finv
  constructor
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx --Goal is x.1 = x.2
  obtain ⟨mid, ⟨hmid1,hmid2⟩⟩ := hx
  exact Fun_output_equal f hf hmid1 hmid2
  intro x hx --Goal is (f ∘ f.inv) x.1 x.2, which is an existence statement
  evaluate finv at x.1 with b hbfinv hbu
  exist b
  refine ⟨hbfinv,?_⟩
  rw [← hx]
  exact hbfinv
  --this direction felt somewhat difficult, can it be simplified somehow?
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  evaluate hf at x.1 with b hbf hbu
  evaluate finv at b with c hcfinv hcu
  obtain finvfx1c : (f.inv ∘ f) x.1 c
  exist b
  refine ⟨hbf,hcfinv⟩
  obtain finvffun : isFunction (f.inv ∘ f) := Fun_comp_fun f f.inv hf finv
  obtain hcx2 : x.2 = c := Fun_output_equal (f.inv ∘ f) finvffun hx finvfx1c
  rw[← hcx2] at hcu
  exact hcu x.1 hbf
  --concludes difficult direction
  intro x hx
  evaluate hf at x.1 with b hbf hbu
  exist b
  refine ⟨hbf,?_⟩
  rw [← hx]
  exact hbf


Conclusion "."
