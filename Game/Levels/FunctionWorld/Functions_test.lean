import Game.Levels.FunctionWorld.L05_Functions


World "FunctionWorld"
Level 6

Title "function"

Introduction "Let's work with one-to-one (or injective) functions in Lean. Check your inventory for the new `Fun_isInjective` definition. Remember, we can't really plug an input into a function without using the `evaluate` tactic, so you might be surprised that the definition also has an arbitrary codomain element in it. It functionally works the same as the definition we know though - to see why, try to prove that the compositum of injective functions is injective.

It might be helpful first to `obtain` that `g ∘ f` is a function - we've already proven this, right?"

/-This problem is some kind of nightmare to think through, what helper lemmas can be earlier levels?-/
Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (g: Rel v w) (hg: isFunction g)  (hgi: isInjective g) : isInjective (g ∘ f) := by
  --This is the original level 5 this file was copied from, can ignore
  sorry

/-This has to be an early functionworld level, I've used it several times-/
theorem Fun_output_equal {u v: Type*} (f: Rel u v) (hf: isFunction f) (a : u) (b c : v) : f a b → f a c → b = c := by
  intro fab fac
  evaluate hf at a with d hdf hdu
  obtain bd := hdu b fab
  obtain cd := hdu c fac
  rw [bd]
  exact cd.symm


/-In levels where you're given a function value, you might want to access the uniqueness statement. This lemma could be used to help you grab it, probably makes sense as an early functionworld level-/
theorem Fun_output_unique {u v: Type*} (f: Rel u v) (hf: isFunction f) (a: u) (b: v) (hab: f a b) : ∀c, f a c → b = c := by
  intro c hc
  exact Fun_output_equal f hf a b c hab hc

/-Maybe this should be a main world level?-/
example {u v: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v u) (hg: isFunction g) (hgf: (g ∘ f) = Rel_id u) : isInjective f := by
  intro a b c fac fbc
  evaluate hg at c with d hdg hdu
  obtain gfad : (g ∘ f) a d := by use c
  obtain gfbd : (g ∘ f) b d := by use c
  rw [hgf] at gfad
  rw [hgf, ← gfad] at gfbd
  exact gfbd.symm








example {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (a : u) (b : v) (c1 c2 : w) (fab : f a b) (gbc1 : g b c1) (gfac2 : (g ∘ f) a c2) : c1 = c2 := by
  sorry

/-Onto level. Maybe simple enough for main world? -/
example {u v: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v u) (hg: isFunction g) (hfg: (f ∘ g) = Rel_id v) : isSurjective f := by
  intro b
  evaluate hg at b with a hag hau
  use a
  evaluate hf at a with c hcg hcu
  obtain fgbc : (f ∘ g) b c := by use a
  rw [hfg] at fgbc
  rw [←fgbc] at hcg
  exact hcg

/-Prove the identity map is a bijection. Currently, the definitions for injective, surjective and bijection don't have a check that the relation is a function. Should they?

Otherwise, this is super easy and likely belongs in the main world.-/
example {u: Type*} : isBijection (Rel_id u) := by
  constructor
  intro a b c hac hbc
  rw [hac, hbc] --rfl not needed
  intro b
  use b
  rfl


/- More composite inj/surj practice-/
example {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (hgf: isSurjective (g ∘ f)) : isSurjective g := by
  intro c
  --Line below unpacks surjectivity condition & composite all at once
  obtain ⟨a,⟨b,⟨hab,hbc⟩⟩⟩ := hgf c
  use b

example {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (hgf: isInjective (g ∘ f)) : isInjective f := by
  intro a1 a2 b fa1b fa2b
  evaluate hg at b with c hcg hcu
  obtain gfa1c : (g ∘ f) a1 c := by use b
  obtain gfa2c : (g ∘ f) a2 c := by use b
  exact hgf a1 a2 c gfa1c gfa2c


example {u v w: Type*} (f g: Rel u v) (hf: isFunction f) (hg: isFunction g) (k: Rel v w) (hk: isFunction k) (hgfgk: (k ∘ f) = (k ∘ g)) (hki: isInjective k) : f = g := by
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  evaluate hf at a with b1 hb1f hb1u
  evaluate hg at a with b2 hb2g hb2u
  evaluate hk at b1 with c1 hc1k hc1u
  evaluate hk at b2 with c2 hc2k hc2u




/- Image/inverse image with inj/surj practice -/
example {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isInjective f) (U: Set u) : invimage f (image f U) = U := by
  apply double_inclusion
  intro a ha
  --Lots of unpacking. Maybe a `Hint` should be given about doing this efficiently?
  obtain ⟨b,⟨⟨c,⟨hc,fbc⟩⟩, fab⟩⟩ := ha
  obtain hac : a = c := hfi a c b fab fbc
  rw [hac]
  exact hc
  intro a ha
  evaluate hf at a with b hbf hbu
  use b
  constructor
  use a
  exact hbf

example {u v: Type*} (f: Rel u v) (hf: isFunction f) (hfi: isSurjective f) (V: Set v) : image f (invimage f V) = V := by
  apply double_inclusion
  intro b hb
  obtain ⟨a, ⟨⟨c,⟨hc,fac⟩⟩,fab⟩⟩ := hb
  obtain hbc : b = c := Fun_output_unique f hf a b fab c fac
  rw[hbc]
  exact hc
  intro b hb
  obtain ⟨a,ha⟩ := hfi b
  use a
  constructor
  use b
  exact ha


/-Fibers form equivalence classes; that is, if R is the relation on u where R a b if and only if g(a) = g(b), then R is an equivalence relation on u. Unsure how to get this into the theorem statement currently-/
example {u v: Type*} (g: Rel u v) (hg: isFunction g) : true := by
  sorry

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


/-Theorems/exercises connecting inverses and bijections-/

example {u v: Type*} (f: Rel u v) (hf: isFunction f) : isFunction f.inv ↔ isBijection f := by
  constructor
  intro finv
  constructor
  intro a b c fac fbc
  --Recall that f a c is definitionally equal to f.inv c a
  exact Fun_output_equal f.inv finv c a b fac fbc
  intro b
  evaluate finv at b with a hafinv hau
  use a
  exact hafinv
  intro h
  obtain ⟨finj,fsurj⟩ := h
  intro b
  obtain ⟨a,ha⟩ := fsurj b
  use! a
  refine ⟨ha,?_⟩
  intro y hy
  exact (finj a y b ha hy).symm

--Final level? Could some earlier levels be used to simplify the work, or maybe break the two directions into two levels?
example {u v: Type*} (f: Rel u v) (hf: isFunction f) : isFunction f.inv ↔ (f ∘ f.inv) = Rel_id v ∧ (f.inv ∘ f) = Rel_id u := by
  constructor
  intro finv
  constructor
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx --Goal is x.1 = x.2
  obtain ⟨mid, ⟨hmid1,hmid2⟩⟩ := hx
  exact Fun_output_equal f hf mid x.1 x.2 hmid1 hmid2
  intro x hx --Goal is (f ∘ f.inv) x.1 x.2, which is an existence statement
  evaluate finv at x.1 with b hbfinv hbu
  use b
  refine ⟨hbfinv,?_⟩
  rw [← hx]
  exact hbfinv
  --this direction felt somewhat difficult, can it be simplified somehow?
  apply Rel_double_inclusion
  apply double_inclusion
  intro x hx
  evaluate hf at x.1 with b hbf hbu
  evaluate finv at b with c hcfinv hcu
  obtain finvfx1c : (f.inv ∘ f) x.1 c := by use b
  obtain finvffun : isFunction (f.inv ∘ f) := Fun_comp_fun f f.inv hf finv
  obtain hcx2 : x.2 = c := Fun_output_equal (f.inv ∘ f) finvffun x.1 x.2 c hx finvfx1c
  rw[← hcx2] at hcu
  exact hcu x.1 hbf
  --concludes difficult direction
  intro x hx
  evaluate hf at x.1 with b hbf hbu
  use b
  refine ⟨hbf,?_⟩
  rw [← hx]
  exact hbf
  --finally to the reverse direction here
  intro ⟨idv,idu⟩ --using brackets in intro can shorten a lot of stuff, just found out it works
  intro b
  obtain hbb : (f ∘ f.inv) b b := by
    rw[idv]
    rfl
  obtain ⟨c,⟨finvbc,fcb⟩⟩ := hbb
  use! c
  refine ⟨fcb,?_⟩
  intro y hy
  obtain finvfyc : (f.inv ∘ f) y c := by
    use b
    refine ⟨hy,fcb⟩
  rw [idu] at finvfyc
  exact finvfyc
