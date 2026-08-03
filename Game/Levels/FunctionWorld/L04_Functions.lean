import Game.Levels.FunctionWorld.L03_Functions


World "FunctionWorld"
Level 4

Title "function"

Introduction "Let's look at images and inverse images of sets. These quantities are of fundamental importance in understanding what a function tells us about relationships between the domain and codomain.

Check your inventory for the new definitions, then try the problem below that will test your understanding of the definitions. You can use `rw` to swap out `image` and `invimage` with their set-builder notation definitions if you'd like, or you can work with them directly."

Statement {u: Type*} (f: Rel_on u) (hf: isFunction f) (C: Set u) : image f C ⊆ C → C ⊆ invimage f C := by
  intro h x hx
  evaluate hf at x with y hyf hyu
  use y
  constructor
  apply h
  use x
  exact hyf

Conclusion "."


/-- If `f : Rel u v` is a function and `U : Set u` is a set of elements of `u`, then `Fun_image f U` is the set of elements `f(u)` where `u ∈ U`.

Since we can't directly "plug in" stuff to `f`, the set `Fun_image f U` is defined as the set of `v ∈ V` with the property that `f u v` for some `u ∈ U`.-/
DefinitionDoc Fun_image as "FUN: Fun_image"


/-- If `f : Rel u v` is a function and `V : Set v` is a set of elements of `v`, then `Fun_invimage f V` is the set of elements of `u` with the property that `f(u) ∈ V`.

Since we can't directly "plug in" stuff to `f`, the set `Fun_invimage f V` is defined as the set of `u ∈ U` with the property that `f u v` for some `v ∈ V`. Of course, we know there is only one such possible `v`, the one we usually call `f(u)`.-/
DefinitionDoc Fun_invimage as "FUN: Fun_invimage"
