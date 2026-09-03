import Game.Levels.FunctionWorld.L01_Functions


World "FunctionWorld"
Level 2

Title "Functions 2"

Introduction "## **Level 2 : The `evaluate` tactic and `Fun_output_equal`**

In practice, we'll rarely need to directly unpack `isFunction f` directly thanks to the `evaluate` tactic. 🔍 Check your inventory for information about `evaluate`.

As the naming suggests, we'll use `evaluate` whenever we need to plug a domain element into a function. There's not a super nice way to do this directly, so don't forget about `evaluate`!

To get some initial practice with `evaluate`, we'll prove a very useful fact for working with functions.

Recall that the point of the uniqueness part of `isFunction f` is that inputs have a unique output. When writing proofs by hand, we use this fact seamlessly by utilizing the `f(x) = y` notation. In Lean, we'll need to be a bit more careful.

We'll often know that `f a b` and `f a c`, at which point `b = c` (the outputs are the same) as long as `f` is a function. Prove this to get some practice with the uniqueness of function outputs."






Statement Fun_output_equal {u v: Type*} {a : u} {b c : v} (f: Rel u v) (hf: isFunction f)  : f a b → f a c → b = c := by
  Hint "👉 Start by naming the assumptions: ```intro fab fbc```"
  intro fab fac
  Hint "👉 Use `evaluate` to access the uniqueness statement for plugging `a` into `f`: ```evaluate hf at a with d hdf hdu```

  This will give the uniqueness statement for plugging in `a` the name `hdu`."
  evaluate hf at a with d hdf hdu
  Hint "From here, use `hdu` to prove that `b = d` and `c = d`. Then we're basically done!"
  obtain bd := hdu b fab
  obtain cd := hdu c fac
  rw [bd,cd]



Conclusion "### **💡 Pro-tip**

It can be a bit weird at first to provide so many names for the output of `evaluate`. If you forget, make sure to 🔍 take a look at `evaluate` in your inventory!"


NewTactic evaluate
NewTheorem Fun_output_equal
