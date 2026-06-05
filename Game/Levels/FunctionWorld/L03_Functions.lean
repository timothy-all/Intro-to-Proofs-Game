import Game.Levels.FunctionWorld.L02_Functions


World "FunctionWorld"
Level 3

Title "function"

Introduction "Let's prove that the compositum of two functions is a function."

/-- If `hf : isFunction f`, the `evaluate` tactic lets us "plug in" `a` to `f`. For instance, `evaluate hf at a with b hbf hbu` will make the output `b` with `hbf` being the information that  `f(a) = b` and `hbu` being the corresponding uniqueness statement. -/
TacticDoc evaluate

/-- The compositum of two functions is also a function. -/
TheoremDoc Fun_comp_fun as "FUN: Fun_comp_fun"

Statement Fun_comp_fun {u v w: Type*} (f: Rel u v) (g: Rel v w) (hf: isFunction f) (hg: isFunction g) : isFunction (g ∘ f):= by
  Hint "Start with `intro a` to grab our arbitrary input."
  intro a
  Hint "So, what does `a` map to? Of course it's g(f(a)), but we have to carefully grab it using our assumptions. In particular, if you try something like `g (f a)`, Lean just gets confused.

  To get `f(a)`, we'll use a new tactic: `evaluate`. If `hf` is the hypothesis guaranteeing that `f` is a function (as it is here), we can write `evaluate hf at a with b hbf hbu`. This grabs `b`, which will play the role of `f(a)`, and sets `hbf` to be the fact that `f(a) = b` and `hbu` to be the fact that `b` is the only possible output for `f`. Try it!"
  evaluate hf at a with b hbf hbu
  Hint "Now we have `b`, and `hbf` is the fact that `f(a) = b` (written as `f a b`, of course)!

  Similarly, obtain `c` such that `g(b) = c`."
  evaluate hg at b with c hcf hcu
  Hint "So, intuitively, `g(f(a)) = c`. Let's prove it: `use! c`. Take it from here!"
  use! c
  constructor
  use b
  intro y hy
  obtain ⟨d, hd⟩ := hy
  obtain db : d = b := by
    apply hbu
    exact hd.left
  apply hcu
  rw [db] at hd
  exact hd.right




Conclusion "."
