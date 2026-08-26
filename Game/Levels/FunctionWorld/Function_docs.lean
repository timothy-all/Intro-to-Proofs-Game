import GameServer



/-- If `R: Rel u v`, `isFunction R` means that `R` is a function from `u` to `v`; that is, for every `a : u`, there is a unique `b : v` such that `R a b`. --/
DefinitionDoc isFunction as "FUN: isFunction"

/--  The identity relation `Rel_id u` on set `u` is a function. -/
TheoremDoc Fun_identity_fun as "FUN: Fun_identity_fun"

/-- If `hf : isFunction f`, the `evaluate` tactic lets us "plug in" `a` to `f`. For instance, `evaluate hf at a with b hbf hbu` will make the output `b` with `hbf` being the information that  `f(a) = b` and `hbu` being the corresponding uniqueness statement. -/
TacticDoc evaluate

/--  If `f` is a function such that `f a b` and `f a c`, then `b = c`. -/
TheoremDoc Fun_output_equal as "FUN: Fun_output_equal"

/-- The compositum of two functions is also a function. In Lean,
```
Fun_comp_fun
{u v w: Type*}
(f: Rel u v)
(g: Rel v w)
(hf: isFunction f)
(hg: isFunction g) :
  isFunction (g ∘ f)
```
Notice that you have to tell Lean that `f` and `g` are functions for this to work. Many theorems about functions require this! -/
TheoremDoc Fun_comp_fun as "FUN: Fun_comp_fun"


/-- If `f : Rel u v` is a function and `U : Set u` is a set of elements of `u`, then `image f U` is the set of elements `f(u)` where `u ∈ U`.

Since we can't directly "plug in" stuff to `f`, the set `image f U` is defined as the set of `v ∈ V` with the property that `f u v` for some `u ∈ U`.-/
DefinitionDoc image as "FUN: image"


/-- If `f : Rel u v` is a function and `V : Set v` is a set of elements of `v`, then `invimage f V` is the set of elements of `u` with the property that `f(u) ∈ V`.

Since we can't directly "plug in" stuff to `f`, the set `invimage f V` is defined as the set of `u ∈ U` with the property that `f u v` for some `v ∈ V`. Of course, we know there is only one such possible `v`, the one we usually call `f(u)`.-/
DefinitionDoc invimage as "FUN: invimage"



/-- If `f : Rel u v` is a function, `isInjective f` means that `f` is one-to-one. This is very slightly different than the typical definition of one-to-one: see the Lean code below.
```
isInjective
{u v : Type*}
(R: Rel u v) :=
  ∀ {a b c}, R a c → R b c → a = b
```
Notice that there's no need to pass `isFunction R` for this to make sense, but the tradeoff is that, without knowing `isFunction R`, there is no way to "plug in" something to `R`. So, we use both input and output values (`R a c` and `R b c`) instead of using just input values and implicitly grabbing output values (such as `f(a)` and `f(b)`). -/
DefinitionDoc isInjective as "FUN: isInjective"

/-- If `f : Rel u v` is a function, `isSurjective f` means that `f` is onto. -/
DefinitionDoc isSurjective as "FUN: isSurjective"


/-- If `f : Rel u v` is a function, `isBijection f` means that `f` is both one-to-one and onto. -/
DefinitionDoc isBijection as "FUN: isBijection"


/-- The identity relation is a bijection. -/
TheoremDoc Fun_identity_bij as "FUN: Fun_identity_bij"


/-- A bijection is invertible. It is important to note that, while the definition of `isBijection` doesn't require the input relation to be a function, this statement does:
```
Fun_bij_is_invertible
{u v: Type*}
(f: Rel u v)
(hf: isFunction f) :
  isBijection f → isFunction f.inv
```-/
TheoremDoc Fun_bij_is_invertible as "FUN: Fun_bij_is_invertible"

/-- Invertible functions are bijections.
```
Fun_invertible_is_bij
{u v: Type*}
(f: Rel u v)
(hf: isFunction f) :
  isFunction f.inv → isBijection f
```
-/
TheoremDoc Fun_invertible_is_bij as "FUN: Fun_invertible_is_bij"


/-- Given a relation `R` from type `u` to type `v`, the corresponding fiber relation relates first coordinates if they share a second coordinate. So it is a relation on `u`. In Lean,
```
Rel_fiberrel
{u v: Type*}
(R: Rel u v) :
  Rel_on u := fun x1 x2 => ∃ y, R x1 y ∧ R x2 y
```
-/
DefinitionDoc Rel_fiberrel as "FUN: Rel_fiberrel"


/-- Compositum of injective functions is injective. There are lots of inputs due to needing to know both inputs are functions:
```
Fun_comp_inj
{u v w: Type*}
(f: Rel u v)
(hf: isFunction f)
(hfi: isInjective f)
(g: Rel v w)
(hg: isFunction g)
(hgi: isInjective g) :
  isInjective (g ∘ f)
``` -/
TheoremDoc Fun_comp_inj as "FUN: Fun_comp_inj"


/-- Compositum of surjective functions is surjective. In Lean:
```
Fun_comp_surj
{u v w: Type*}
(f: Rel u v)
(hfs: isSurjective f)
(g: Rel v w)
(hgs: isSurjective g)
  : isSurjective (g ∘ f)
```
This doesn't actually use that the relations are functions, so there are no `isFunction` hypotheses!-/
TheoremDoc Fun_comp_surj as "FUN: Fun_comp_surj"
