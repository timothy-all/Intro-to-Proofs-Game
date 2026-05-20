import Game.Levels.FunctionWorld.L01_Functions


World "FunctionWorld"
Level 2

Title "function"

Introduction "In the Intro to Proofs game, we'll always view functions first and foremost as relations - no `y = f(x)`. Despite this, if `f: Rel u v` and `a : u`, Lean makes sense out of `f a`. We can think intuitively of this as meaning `f(a)`, but that's not exactly right, though it often helps with intuition.

Let's start to examine this with the following theorem that we state for functions in class - we can prove two functions are equal if they're equal on all of their possible inputs. But we won't need `isFunction` to do it. Let's see what happens."

/--  We can check if two relations are equal by proving that, if you take an arbitrary first coordinate, all the second coordinates are the same. -/
TheoremDoc Rel_equal_if_equal_inputs as "FUN: Rel_equal_if_equal_inputs"

Statement Rel_equal_if_equal_inputs {u v: Type*} (f g: Rel u v) (hf: isFunction f) (hg: isFunction g) : (∀ a : u, f a = g a) → f = g := by
  Hint "Start with `intro h` to name our hypothesis."
  intro h
  Hint "Remember that double inclusion is the typical way that we prove relations are equal, so let's do that here. `apply Rel_double_inclusion` then `apply double_inclusion` to begin the double inclusion proof."
  apply Rel_double_inclusion
  apply double_inclusion
  Hint "Finally, `intro x hx` to unpack the forward direction of double inclusion."
  intro x hx
  Hint "Remember that `x ∈ f.set` means that `f x.1 x.2`. So our goal is to show that `g x.1 x.2`.

  In general, for a relation, it's not guaranteed that `g` has any ordered pairs containing `x.1` or `x.2`. But since `g` is a function, it has an ordered pair with first coordinate `x.1` guaranteed! Then `f a = g a` guarantees the same second coordinate.

  Let's start by plugging in `x.1` to `h`: `obtain hplug : f x.1 = g x.1 := h x.1`."
  obtain hplug : f x.1 = g x.1 := h x.1
  Hint "From here, show that `g x.1 x.2`, then tackle the reverse inclusion similarly."
  obtain gx1x2 : g x.1 x.2 := by
    rw [←hplug]
    exact hx
  exact gx1x2
  intro x hx
  obtain hplug : f x.1 = g x.1 := h x.1
  obtain fx1x2 : f x.1 x.2 := by
    rw [hplug]
    exact hx
  exact fx1x2




Conclusion "So what's going on here? `f a = g a` in Lean means that `f` and `g` always have the same second coordinate when their first coordinate is `a`, even if there are several second coordinates with first coordinate `a`.

In the next level, we'll examine another basic theorem that does in fact require the function property!"
