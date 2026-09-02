import Game.Levels.FunctionWorld.L12_Functions


World "FunctionWorld"
Level 13

Title "Functions 13"

Introduction "## **Level 13 : Invertible functions have two-sided inverses**

This is the converse of the last level, a fitting boss for FunctionWorld!"

/-- An invertible function composes with its inverse to the identity in both orders.-/
Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfinv: isFunction f.inv): (f ∘ f.inv) = Rel_id v ∧ (f.inv ∘ f) = Rel_id u  := by
  constructor
  apply Rel_double_inclusion
  apply Double_inclusion
  intro x hx --Goal is x.1 = x.2
  obtain ⟨mid, ⟨hmid1,hmid2⟩⟩ := hx
  exact Fun_output_equal f hf hmid1 hmid2
  intro x hx --Goal is (f ∘ f.inv) x.1 x.2, which is an existence statement
  evaluate hfinv at x.1 with b hbfinv hbu
  exist b
  refine ⟨hbfinv,?_⟩
  rw [← hx]
  exact hbfinv
  --this direction felt somewhat difficult, can it be simplified somehow?
  apply Rel_double_inclusion
  apply Double_inclusion
  intro x hx
  evaluate hf at x.1 with b hbf hbu
  evaluate hfinv at b with c hcfinv hcu
  obtain finvfx1c : (f.inv ∘ f) x.1 c
  exist b
  refine ⟨hbf,hcfinv⟩
  obtain finvffun : isFunction (f.inv ∘ f) := Fun_comp_fun f f.inv hf hfinv
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


Conclusion "Congratulations, you've beaten Function World! This was by far your most difficult Lean challenge yet. Continue onto Induction World to explore another proof technique."
