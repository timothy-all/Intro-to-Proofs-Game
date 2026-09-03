import Game.Levels.FunctionWorld.L08_Functions


World "FunctionWorld"
Level 9

Title "Functions 9"

Introduction "## **Level 9 : Function property mini-boss**

Try to prove the theorem below - it's a bit more difficult than previous levels in this world, but you've got this!"

/-- If $f : u → v$ is injective and $U$ is a set of elements of $u$, then $f^{-1}(f(U)) = U.$-/
Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (U: Set u) : invimage f (image f U) = U := by
  Hint "As the goal is a set equality, let's do a double inclusion proof. 👉 Start with ```apply Double_inclusion``` then ```intro a ha``` to grab an arbitrary element toward the first inclusion."
  apply Double_inclusion
  intro a ha
  Hint "There is a huge amount of unpacking to be done with the hypothesis `ha` - the definitions of both `invimage` and `image` are both existentially quantified. You should try unpacking it step-by-step yourself, say by starting with 👉 ```obtain ⟨b, hb⟩ := ha``` but everything can ultimately be unpacked at once with the monstrous `obtain ⟨b,⟨⟨c,⟨hc,fbc⟩⟩, fab⟩⟩ := ha`!"
  obtain ⟨b,⟨⟨c,⟨hc,fbc⟩⟩, fab⟩⟩ := ha
  Hint "Last hint for this one: you have enough unpacked to be able to use f's injectivity to close the goal. You've got this!"
  obtain hac : a = c := hfi fab fbc
  rw [hac]
  exact hc
  intro a ha
  evaluate hf at a with b hbf hbu
  exist b
  refine ⟨?_,hbf⟩
  exist a
  refine ⟨ha, hbf⟩


Conclusion "There's a similar version of this theorem for surjective functions, but it's not as simple as replacing the injective assumption with a surjective one. Can you figure out how to modify it?"
