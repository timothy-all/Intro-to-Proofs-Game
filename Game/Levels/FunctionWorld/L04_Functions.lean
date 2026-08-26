import Game.Levels.FunctionWorld.L03_Functions


World "FunctionWorld"
Level 4

Title "function"

Introduction "Let's look at images and inverse images of sets. These quantities are of fundamental importance in understanding what a function tells us about relationships between the domain and codomain.

Check your inventory for the new definitions, then try the problem below that will test your understanding of the definitions. You can use `rw` to swap out `image` and `invimage` with their set-builder notation definitions if you'd like, or you can work with them directly."

Statement {u: Type*} (f: Rel_on u) (hf: isFunction f) (C: Set u) : image f C ⊆ C → C ⊆ invimage f C := by
  intro h x hx
  evaluate hf at x with y hyf hyu
  exist y
  constructor
  apply h
  exist x
  refine ⟨hx,hyf⟩
  exact hyf

Conclusion "."


NewDefinition image invimage
