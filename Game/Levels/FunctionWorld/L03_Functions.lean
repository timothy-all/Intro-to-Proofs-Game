import Game.Levels.FunctionWorld.L02_Functions


World "FunctionWorld"
Level 3

Title "function"

Introduction "Let's prove that the compositum of two functions is a function."



Statement Fun_comp_fun {u v w: Type*} (f: Rel u v) (g: Rel v w) (hf: isFunction f) (hg: isFunction g) : isFunction (g ∘ f):= by
  Hint "Start with `intro a` to grab our arbitrary input."
  intro a
  Hint "So, what does `a` map to? Of course it's g(f(a)); we'll have to use `evaluate` carefully to access it. First, `evaluate hf at a with b hbf hbu` to plug `a` into `f`."
  evaluate hf at a with b hbf hbu
  Hint "Now, similarly, use `evaluate` to plug `b` into `g`. Call the output `c`."
  evaluate hg at b with c hcf hcu
  Hint "So, intuitively, `g(f(a)) = c`. Let's prove it: `exist! c`. Take it from here! It might continue to be helpful to use `Fun_output_equal` as you work through what has to be shown."
  exist! c
  exist b
  refine ⟨hbf,hcf⟩
  intro y hy
  obtain ⟨d, ⟨fad,gdy⟩⟩ := hy
  obtain db : b = d := Fun_output_equal f hf hbf fad
  rw [←db] at gdy
  exact Fun_output_equal g hg gdy hcf




Conclusion "."

NewTheorem Fun_comp_fun
