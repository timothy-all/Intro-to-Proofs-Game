import Game.Levels.FunctionWorld.L04_Functions


World "FunctionWorld"
Level 5

Title "function"

Introduction "Let's work with one-to-one (or injective) functions in Lean. Check your inventory for the new `Fun_isInjective` definition. Remember, we can't really plug an input into a function without using the `evaluate` tactic, so you might be surprised that the definition also has an arbitrary codomain element in it. It functionally works the same as the definition we know though - to see why, try to prove that the compositum of injective functions is injective.

It might be helpful first to `obtain` that `g ∘ f` is a function - we've already proven this, right?"

/-This problem is some kind of nightmare to think through, what helper lemmas can be earlier levels?-/
Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: Fun_isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: Fun_isInjective g) : Fun_isInjective (g ∘ f) := by
  intro a b c gfac gfbc
  obtain gffun := Fun_comp_fun f g hf hg
  evaluate hf at a with y1 hy1
  evaluate hf at b with y2 hy2
  evaluate hg at y1 with z1 hz1
  evaluate hg at y2 with z2 hz2
  obtain gfaz1 : (g ∘ f) a z1 := by
    use y1
    refine ⟨hy1.left,hz1.left⟩
  obtain gfbz2 : (g ∘ f) b z2 := by
    use y2
    refine ⟨hy2.left,hz2.left⟩
  obtain hz1z2 : z1 = z2 := by
    evaluate gffun at a with w1 hw1
    evaluate gffun at b with w2 hw2
    obtain hcw1 : c = w1 := hw1.right c gfac
    obtain hcw2 : c = w2 := hw2.right c gfbc
    obtain hz1w1 : z1 = w1 := hw1.right z1 gfaz1
    obtain hz2w2 : z2 = w2 := hw2.right z2 gfbz2
    rw [hz1w1, hz2w2,←hcw1,←hcw2]
  rw [hz1z2] at hz1
  obtain hy1y2 : y1 = y2 := hgi y1 y2 z2 hz1.left hz2.left
  rw [hy1y2] at hy1
  exact hfi a b y2 hy1.left hy2.left


example {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: Fun_isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: Fun_isInjective g) : Fun_isInjective (g ∘ f) := by
  intro a b c gfac
  contrapose!
  intro ne
  rw[Rel_comp]
  push_neg
  intro x fbx
  by_contra! gxc
  evaluate hf at a with y hy
  obtain gyc : g y c
  sorry
  obtain this := hgi x y c gxc gyc
  rw[this] at fbx
  obtain that := hfi a b y hy.left fbx
  contradiction


Conclusion "."
