import Game.Levels.FunctionWorld.L05_Functions


World "FunctionWorld"
Level 23

Title "function"

Introduction "functionworld problem bank"

Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: isInjective g) : isInjective (g ∘ f) := by
  --This is the original level 5 this file was copied from, can ignore
  sorry



/-In levels where you're given a function value, you might want to access the uniqueness statement. This lemma could be used to help you grab it, probably makes sense as an early functionworld level-/
--theorem Fun_output_unique {u v: Type*} (f: Rel u v) (hf: isFunction f) (a: u) (b: v) (hab: f a b) : ∀c, f a c → b = c := by
  --intro c hc
  --exact Fun_output_equal f hf a b c hab hc


/-Example below could be a nice level?-/
example {u v : Type*} (f: Rel u v) (g: Rel u v) (hf: isFunction f) (hg: isFunction g) (h: ∀ a, ∃ b, f a b = g a b) : f = g := by
  --Hint "The hypothesis `h` is the way we're saying that `f` and `g` have the same output for each input. Notice that this, by itself, is weaker than `f` and `g` being the same relation because **only one** `b` is being checked. But, since `f` and `g` are functions, we know only one `b` is possible!
  --
  --Start by applying `Rel_double_inclusion` and `double_inclusion`."
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  sorry
  sorry





example {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (a : u) (b : v) (c1 c2 : w) (fab : f a b) (gbc1 : g b c1) (gfac2 : (g ∘ f) a c2) : c1 = c2 := by
  sorry


/-Currently, the definitions for injective, surjective and bijection don't have a check that the relation is a function. Should they?
-/


/- More composite inj/surj practice-/
example {u v w: Type*} (f g: Rel u v) (hf: isFunction f) (hg: isFunction g) (k: Rel v w) (hk: isFunction k) (hgfgk: (k ∘ f) = (k ∘ g)) (hki: isInjective k) : f = g := by
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  evaluate hf at x.1 with b1 hb1f hb1u
  evaluate hg at x.1 with b2 hb2g hb2u
  evaluate hk at b1 with c1 hc1k hc1u
  evaluate hk at b2 with c2 hc2k hc2u
  sorry
  sorry
  /-not done-/






/- Image/inverse image with inj/surj practice -/

/-exampleworld-/


Conclusion "."
