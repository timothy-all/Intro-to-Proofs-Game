import Game.Levels.FunctionWorld.L03_Functions


World "FunctionWorld"
Level 4

Title "Functions 4"

Introduction "## **Level 4 : Images and inverse images**

Let's look at images and inverse images of sets. These quantities are of fundamental importance in understanding what a function tells us about relationships between the domain and codomain.

🔍 Check your inventory for the new definitions, then try the problem below that will test your understanding of the definitions. You can use `rw` to swap out `image` and `invimage` with their set-builder notation definitions if you'd like, or you can work with them directly."

/--Suppose $f: A → A$ and $C ⊆ A$. If $f(C) ⊆ C$, then $C ⊆ f^{-1}(C).$ -/
Statement {u: Type*} (f: Rel_on u) (hf: isFunction f) (C: Set u) : image f C ⊆ C → C ⊆ invimage f C := by
  Hint "👉 Let's ```intro h``` to grab our image hypothesis, then ```intro x hx``` to take an arbitrary element of `C` that we'll prove is in the inverse image of `C`."
  intro h x hx
  Hint "To show `x ∈ invimage f C`, we have to find `y ∈ C` with `f x y`. Since `f` is a function, certainly we just *plug in x*, right? So let's use our new `evaluate` tactic to get `y`! 👉 Try ```evaluate hf at x with y hyf hyu```"
  evaluate hf at x with y hyf hyu
  Hint "Now we can provide `y` for our existence goal using 👉 ```exist y``` Take it from here!"
  exist y
  constructor
  apply h
  exist x
  refine ⟨hx,hyf⟩
  exact hyf

Conclusion "The converse of the goal is also true - let's look at it in the next level!"


NewDefinition image invimage
