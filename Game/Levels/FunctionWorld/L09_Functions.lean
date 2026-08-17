import Game.Levels.FunctionWorld.L08_Functions


World "FunctionWorld"
Level 9

Title "function"

Introduction "Try to prove the theorem below - it's a bit more difficult than previous levels in this world, but you've got this!"

Statement {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (U: Set u) : invimage f (image f U) = U := by
  apply double_inclusion
  intro a ha
  --Lots of unpacking. Maybe a `Hint` should be given about doing this efficiently?
  obtain ⟨b,⟨⟨c,⟨hc,fbc⟩⟩, fab⟩⟩ := ha
  obtain hac : a = c := hfi fab fbc
  rw [hac]
  exact hc
  intro a ha
  evaluate hf at a with b hbf hbu
  use b
  constructor
  use a
  exact hbf


Conclusion "."
