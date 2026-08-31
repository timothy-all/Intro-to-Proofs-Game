import Game.Levels.FunctionWorld.L05_Functions


World "FunctionWorld"
Level 6

Title "Functions 6"

Introduction "## **Level 6 : Injective (one-to-one) Functions**

Let's work toward using bijections and inverses in Lean. We'll start with one-to-one functions: 🔍 check your inventory for the new `isInjective` definition. Remember, we can't really plug an input into a function without using the `evaluate` tactic, so you might be surprised that the definition also has an arbitrary codomain element in it. It functionally works the same as the definition we know though!"

/--If $f$ and $g$ are functions such that $g ∘ f$ is injective, then $f$ must be injective.-/
Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (hgf: isInjective (g ∘ f)) : isInjective f := by
  Hint "As you should've seen in your inventory, there's quite a lot of inputs for `isInjective f` - three arbitrary elements, and two hypotheses. So we'll need to intro all of them (with descriptive names because there's so many): 👉 `intro a1 a2 b fa2b fa2b`"
  intro a1 a2 b fa1b fa2b
  Hint "We know `g ∘ f` is injective, so if we want to use that, we're going to have to bring `g` into the picture. Of course, by plugging `b` into `g` (say, with output `c`) we'll know `(g ∘ f) a1 c` and `(g ∘ f) a2 c`. So we'll need evaluate: 👉 `evaluate hg at b with c hcg hcu`."
  evaluate hg at b with c hcg hcu
  Hint "From here, use 👉 `obtain gfa1c : (g ∘ f) a1 c` to get `(g ∘ f) a1 c` as a hypothesis. Of course, a separate goal will open and you'll have to prove that this is true! Then you can finish from here."
  obtain gfa1c : (g ∘ f) a1 c
  exist b
  refine ⟨fa1b,hcg⟩
  obtain gfa2c : (g ∘ f) a2 c
  exist b
  refine ⟨fa2b,hcg⟩
  exact hgf gfa1c gfa2c


Conclusion "`isInjective` truly has a monstrous number of arguments, and it's not the most complicated thing we'll be working with. Never forget that you can review what's needed to use each definition by looking at it in your 🔍 Inventory!"

NewDefinition isInjective
