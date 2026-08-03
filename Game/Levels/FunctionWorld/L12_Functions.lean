import Game.Levels.FunctionWorld.L11_Functions


World "FunctionWorld"
Level 12

Title "function"

Introduction "Lastly, let's see how you can check that a function is invertible by getting the identity function by composing the function with its inverse relation in both directions.

This one's pretty challenging!"

Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) : (f ∘ f.inv) = Rel_id v ∧ (f.inv ∘ f) = Rel_id u → isFunction f.inv  := by
  intro ⟨idv,idu⟩
  intro b
  obtain hbb : (f ∘ f.inv) b b := by
    rw[idv]
    rfl
  obtain ⟨c,⟨finvbc,fcb⟩⟩ := hbb
  use! c
  refine ⟨fcb,?_⟩
  intro y hy
  obtain finvfyc : (f.inv ∘ f) y c := by
    use b
    refine ⟨hy,fcb⟩
  rw [idu] at finvfyc
  exact finvfyc


Conclusion "."
