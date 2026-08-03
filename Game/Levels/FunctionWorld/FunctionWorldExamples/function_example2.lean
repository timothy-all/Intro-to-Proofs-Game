import Game.Levels.FunctionWorld.FunctionWorldExamples.function_example1


World "FunctionWorldExamples"
Level 2

Title "f"

Introduction "A function that is an equivalence relation can only be the identity function."


Statement {u: Type*} (f: Rel_on u) (hf: isFunction f) (hfe: isEquivalence f) : f = Rel_id u := by
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  evaluate hf at x.1 with b hbf hbu
  obtain hbx1 : x.1 = b := hbu x.1 (hfe.refl x.1)
  obtain hbx2 : x.2 = b := hbu x.2 hx
  rw [← hbx2] at hbx1
  exact hbx1
  intro x hx
  obtain fx1x1 : f x.1 x.1 := hfe.refl x.1
  nth_rw 2 [hx] at fx1x1 --Can we use nth_rw? Way around it?
  exact fx1x1





Conclusion "."
