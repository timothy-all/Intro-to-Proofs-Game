import Game.Levels.FunctionWorld.L06_Functions


World "FunctionWorld"
Level 7

Title "function"

Introduction "Now let's do a straightforward onto example."

Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (hgf: isSurjective (g ∘ f)) : isSurjective g := by
  intro c
  --Line below unpacks surjectivity condition & composite all at once
  obtain ⟨a,⟨b,⟨hab,hbc⟩⟩⟩ := hgf c
  exist b
  exact hbc


Conclusion "."

NewDefinition isSurjective
