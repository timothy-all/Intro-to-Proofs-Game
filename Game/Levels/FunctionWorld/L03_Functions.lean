import Game.Levels.FunctionWorld.L02_Functions


World "FunctionWorld"
Level 3

Title "function"

Introduction "Let's prove that the compositum of two functions is a function."

/-- If `hf : isFunction f`, the `evaluate` tactic lets us "plug in" `a` to `f`. For instance, `evaluate hf at a with b hb` will make the output `b` with `hb` being the information required for `f(a) = b`. -/
TacticDoc evaluate

Statement {u v w: Type*} (f: Rel u v) (g: Rel v w) (hf: isFunction f) (hg: isFunction g) : isFunction (g ∘ f):= by
  Hint "Start with `intro a` to grab our arbitrary input."
  intro a
  Hint "So, what does `a` map to? Of course, it's g(f(a)), but we have to carefully grab it using our assumptions. In particular, if you try something like `g (f a)`, Lean just gets confused.

  To get `f(a)`, we'll use a new tactic: `evaluate`. If `hf` is the hypothesis guaranteeing that `f` is a function (as it is here), we can write `evaluate hf at a with b hb`. This grabs `b`, which will play the role of `f(a)`, and sets `hb` to be the properties required for `b` to be `f(a)`. Try it!"
  evaluate hf at a with b hb
  Hint "Now we have `b`, and `hb.left` is the fact that `f(a) = b` (written as `f a b`, of course)!

  Similarly, obtain `c` such that `g(b) = c`."
  evaluate hg at b with c hc
  Hint "So, intuitively, `g(f(a)) = c`. Let's prove it: `use! c`. Take it from here!"
  use! c
  constructor
  use b
  constructor
  exact hb.left
  exact hc.left
  intro y hy
  obtain ⟨d, hd⟩ := hy
  obtain db : d = b := by
    apply hb.right
    exact hd.left
  apply hc.right
  rw [db] at hd
  exact hd.right



Conclusion "."
