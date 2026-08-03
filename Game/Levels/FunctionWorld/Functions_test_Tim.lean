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

def Rel_fiberrel {u v : Type*} (g : Rel u v) : Rel_on u := by
  intro x y
  exact ∃ z : v, g x z ∧ g y z

/-Fibers form equivalence classes; that is, if R is the relation on u where R a b if and only if g(a) = g(b), then R is an equivalence relation on u. Unsure how to get this into the theorem statement currently-/
example {u v: Type*} (g: Rel u v) (hg: isFunction g) : isEquivalence (Rel_fiberrel g)  := by
  constructor
  intro x
  evaluate hg at x with y hgx hgu
  use y
  intro x y h
  rcases h with ⟨z,hz1,hz2⟩
  use z
  intro a b c ⟨z,hz1,hz2⟩ ⟨w,hw1,hw2⟩
  use w
  refine ⟨?_,hw2⟩
  obtain eq := Fun_output_equal g hg b z w hz2 hw1
  rw[← eq]
  exact hz1

/-Fun function exercise. Only uses that f is a function and f is reflexive, could replace equivalence with reflexive but without it students have to figure out that it's reflexive that matters-/
example {u: Type*} (f: Rel_on u) (hf: isFunction f) (hfe: isEquivalence f) : f = Rel_id u := by
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  evaluate hf at x.1 with b hbf hbu
  obtain hbx1 : x.1 = b := hbu x.1 (hfe.refl x.1)
  obtain hbx2 : x.2 = b := hbu x.2 hx
  rw [← hbx2] at hbx1
  exact hbx1
  intro x hx
  obtain fx1x1 : f x.1 x.1 := hfe.refl x.1
  nth_rw 2 [hx] at fx1x1 --Can we use nth_rw? Way around it?
  exact fx1x1

Conclusion "."
