import Game.Levels.FunctionWorld.L02_Functions


World "FunctionWorld"
Level 3

Title "function"

Introduction "Let's prove that the compositum of two functions is a function."



Statement {u v w: Type*} (f: Rel u v) (g: Rel v w) (hf: isFunction f) (hg: isFunction g) : isFunction (g ∘ f):= by
  Hint "Start with `intro a` to grab our arbitrary input."
  intro a
  Hint "So, what does `a` map to? Of course, it's g(f(a)), but we have to carefully grab it using our assumptions. In particular, if you try something like `g (f a)`, Lean just gets confused.

  Let's start by grabbing f(a). Intuitively, this is the unique `b` such that `f a b` is true. So we start by plugging `a` into `hf`: `obtain hfa := hf a`."
  obtain hfa := hf a
  Hint "Now we just need the existence part of the existence & uniqueness statement (for now).

  So, grab `b`: `obtain ⟨b, hb⟩ := hfa; dsimp at hb`. (Without the dsimp, Lean will display some weird trivial function evaluations. Don't worry about it too much.)"
  obtain ⟨b, hb⟩ := hfa; dsimp at hb
  Hint "Now we have `b`, and `hb.left` is the fact that `f(a) = b`! Similarly, obtain `c` such that `g(b) = c`. We can do it in one line: `obtain ⟨c, hc⟩ := hg b; dsimp at hc`"
  obtain ⟨c, hc⟩ := hg b; dsimp at hc
  Hint "Finally, we can `use! c`. Take it from here!"
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
