import Game.Levels.FunctionWorld.L11_Functions


World "FunctionWorld"
Level 12

Title "Functions 12"

Introduction "## **Level 12 : Functions with two-sided inverses are invertible**

Let's see how you can check that a function is invertible by getting the identity function by composing the function with its inverse relation in both directions. This is used all the time to check that functions defined by explicit formulas are invertible!

This one's pretty challenging, but you have all the required tools!"

/--A function that composes with its inverse relation to the identity in both orders is invertible.-/
Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfrightinv: (f ∘ f.inv) = Rel_id v) (hfleftinv: (f.inv ∘ f) = Rel_id u) : isFunction f.inv  := by
  intro b
  obtain hbb : (f ∘ f.inv) b b := by
    rw[hfrightinv]
    rfl
  obtain ⟨c,⟨finvbc,fcb⟩⟩ := hbb
  exist! c
  exact fcb
  intro y hy
  obtain finvfyc : (f.inv ∘ f) y c := by
    exist b
    refine ⟨hy,fcb⟩
  rw [hfleftinv] at finvfyc
  exact finvfyc


Conclusion "The converse is even more challenging..."
