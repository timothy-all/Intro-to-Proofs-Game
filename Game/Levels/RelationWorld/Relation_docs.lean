import GameServer


/--
This is the **set** Cartesian product symbol, used in set Cartesian product levels found in RelationWorld and RelationWorldExamples. So, if `A` is a set of elements from type `u` and `B` is a set of elements from type `v` (in Lean: `A : Set u`, `B: Set v`),
 ```
A ×ˢ B = { (a,b) | a ∈ A ∧ b ∈ B}.
```
If `p ∈ A ×ˢ B`, you can access the coordinates of `p` by using `p.1` and `p.2` (or `p.fst` and `p.snd` - first and second).

To type this symbol, write `\xs`.
-/
DefinitionDoc Set.prod as "REL: ×ˢ"


/--
This tells us what it means to be a member of the Cartesian product of two **sets**. Here's how it looks in Lean:
```
mem_prod_iff
{u v : Type*}
{x : u}
{y : v}
(A : Set u)
(B : Set v)
(p : u × v) :
  p ∈ A ×ˢ B ↔ p.1 ∈ A ∧ p.2 ∈ B
```
Notice that `p` has type `u × v` - this is the **type** Cartesian product that is used extensively when talking about relations. It shows up here because `p` is an ordered pair that is not, a priori, known to have coordinates living in any sets.
-/
DefinitionDoc mem_prod_iff as "REL: mem_prod_iff"


/--
This tells us what it means not to be an element of the Cartesian product of two **sets**. In Lean:
```
Not_mem_prod
{u v: Type*}
{x : u}
{y : v}
(A: Set u)
(B: Set v)
(h: (x,y) ∉ (A ×ˢ B)) :
  x ∉ A ∨ y ∉ B
```
-/
TheoremDoc Not_mem_prod as "REL: Not_mem_prod"

/--
An ordered pair `(a,b)` fails to be in the Cartesian product `A ×ˢ B` as long as `a ∉ A`. In Lean,
```
Fst_not_mem_not_mem_prod
{u v: Type*}
(A: Set u)
(B: Set v)
(x : u)
(y: v)
(h: x ∉ A) :
  (x,y) ∉ (A ×ˢ B)
```
-/
TheoremDoc Fst_not_mem_not_mem_prod as "REL: Fst_not_mem_not_mem_prod"


/-- Swaps out relation equality with the underlying set equality. In Lean,
```
Rel_double_inclusion
{u v: Type*}
(R: Rel u v)
(S: Rel u v) :
  R.set = S.set → R = S
```
Of course it is also true that `R = S → R.set = S.set`, but the proof of this is just a simple `rw`.
-/
TheoremDoc Rel_double_inclusion as "REL: Rel_double_inclusion"


/-- `R.inv` is the inverse of the relation `R`. More precisely, `R a b` means `R.inv b a`. Further, these are *definitionally equal*; for example, if your goal is `⊢ R a b` and you know `h : R.inv b a`, `exact h` will close the goal. --/
DefinitionDoc Rel.inv as "REL: Rel.inv"

/-- If `R : Rel u v`, `R.pairs` is the set of ordered pairs `(x,y)` with the property that `R x y`. Precisely,
```R.pairs = {(a,b) | R a b}```
If `x : u × v`, the statement `x ∈ R.pairs` is definitionally equal to `R x.1 x.2`.
-/
DefinitionDoc Rel.pairs as "REL: Rel.pairs"


/-- The inverse of the inverse of a relation is itself. In Lean,
```
Rel_inv_inv
{u v : Type}
(R: Rel u v) :
  (R.inv).inv = R
```
-/
TheoremDoc Rel_inv_inv as "REL: Rel_inv_inv"

/-- If `R` is a relation from `u` to `v` and `S` is a relation from `v` to `w`, then `S ∘ R` is a relation from `u` to `w` defined in the following way: `(S ∘ R) a c` as long as there exists `b` with the property that `R a b` and `S b c`. This means that if you want to *prove* `(S ∘ R) a c` you have to *provide* `b` (say, by using the `exists` tactic), and if you have `h : (S ∘ R) a c` you can use `obtain` to *grab* `b`.

# **⌨ Typesetting Tip**

To get the composition circle ∘, you can type "\circ".
-/
DefinitionDoc Rel.comp as "REL: ∘"

/-- `R.dom` is the domain of the relation `R`. This is a **set**:
```
R.dom = { a | ∃ b, R a b }
```
-/
DefinitionDoc Rel.dom as "REL: Rel.dom"

/--
`R.range` is the range of the relation `R`. This is a **set**:
```
R.range = { b | ∃ a, R a b }
```
-/
DefinitionDoc Rel.range as "REL: Rel.range"

/-- `Rel_on u` is shorthand for `Rel u u`. So, if you have `R : Rel_on u`, all facts about `Rel`s can be used for `R`; for instance, `R.pairs` makes sense and works the exact same as if `R` were of type `Rel u u`.
-/
DefinitionDoc Rel_on as "REL: Rel_on"

/-- `Rel_id u` is the identity relation on the universe (type) `u`. Under the hood, this is how it's defined:
```
Rel_id
(u : Type*) :
  Rel_on u := fun u1 u2 => u1 = u2
```
The `fun` keyword tells Lean we're providing "function" inputs - this works here because, in Lean, a relation is a function whose output is a proposition, and that proposition's truth value tells is whether the inputs are related. So, for the identity relation, that proposition is simply equality.
 -/
DefinitionDoc Rel_id as "REL: Rel_id"


/-- The `nth_rw` tactic does a targeted rewrite of the goal at only a specific position. For instance, `nth_rw 2 [h]` will swap out whatever equality `h` gives at the second place it occurs in the goal.

You can also do `nth_rw 2 [h] at k` to do the same thing to hypothesis `k`. -/
TacticDoc nth_rw


/--Replaces the `set` of the identity relation on `u` with the more concrete set of ordered pairs of the form `(a,a)`. In Lean,
```
Rel_id_pairs
{u : Type} :
  (Rel_id u).pairs = {(a,a) | a : u}
```-/
TheoremDoc Rel_id_pairs as "REL: Rel_id_pairs"



/-- Makes a relation `R` reflexive. In Lean,
```
isReflexive
{u : Type*}
(R: Rel_on u) :=
  ∀ a, R a a
```
For instance, if we have `R : Rel_on u` and `h : isReflexive R`, we can "plug in" any `a : u` to `h` to get the proof that `R a a`. More directly, `h a` is the same as `R a a`.-/
DefinitionDoc isReflexive as "REL: isReflexive"

/-- Makes a relation `R` symmetric. In Lean,
```
isSymmetric
{u : Type*}
(R: Rel_on u) :=
  ∀ {a b}, (R a b) → (R b a)
```
For instance, if we have `R : Rel_on u` and `h : isSymmetric R`, we can "plug in" any `a : u` and `b : u` to `h` to get the proof that `R a b → R b a`. More directly, `h a b` is the same as `R a b → R b a`. Further, if we also know `k : R a b`, we can use `h` to get `R b a` by writing `h a b k`.-/
DefinitionDoc isSymmetric as "REL: isSymmetric"

/-- Makes a relation `R` anti-symmetric. In Lean,
```
isAntisymmetric
{u : Type*}
(R: Rel_on u)
  := ∀ {a b}, ((R a b) ∧ (R b a)) → a = b
```
For instance, if we have `R : Rel_on u` and `h : isAntiSymmetric R`, we can "plug in" any `a : u` and `b : u` to `h` to get the proof that `(R a b ∧ R b a) → a = b`. More directly, `h a b` is the same as `(R a b ∧ R b a) → a = b`. -/
DefinitionDoc isAntisymmetric as "REL: isAntiymmetric"

/-- Makes a relation `R` transitive. In Lean,
```
 isTransitive
 {u : Type*}
 (R: Rel_on u)
  := ∀ {a b c}, (R a b) → (R b c) → (R a c)
```
For instance, if we have `R : Rel_on u` and `h : isTransitive`, we can "plug in" any `a : u`, `b : u`, and `c : u` to `h` to get the proof that `R a b → R b c → R a c`. This definition uses *currying* to simplify its applications -- it is logically equivalent to the perhaps more familiar `(R a b ∧ R b c) → R a c`. For instance, if we know `k : R a b` and `l : R b c`, then `h k l` is the proof that `R a c`, without resorting to any `And.intro` shenanigans. -/
DefinitionDoc isTransitive as "REL: isTransitive"

/-- Makes a relation `R` an equivalence relation. If we know `R : Rel_on u` and `eq : isEquivalence R`, we can access the reflexive, symmetric, and transitive properties of `R` by writing `eq.refl`, `eq.symm`, and `eq.tran`, respectively. For example, if `a : u`, `eq.refl a` is the same as `R a a`.  -/
DefinitionDoc isEquivalence as "REL: isEquivalence"

/-- Makes a relation `R` a partial order. If we know `R : Rel_on u` and `po: isPartialOrder R`, use `po.refl`, `po.anti`, `po.tran` to access the reflexive, anti-symmetric, and transitive properties, respectively. For example, if `a : u`, `po.refl a` is the same as `R a a`-/
DefinitionDoc isPartialOrder as "REL: isPartialOrder"

/-- If `R` is a relation on `u`, `isMinimal R b` means that `b` is a minimal element of `u`. In Lean,
```
isMinimal
{u : Type*}
(R: Rel_on u)
(b : u)
(B : Set u := Set.univ) :=
  b ∈ B ∧ ∀ x, x ∈ B → R x b → x = b
```
The statement `B : Set u := Set.univ` means that the *default value* passed to `isMinimal` for that argument is `Set.univ`. So, if we want to specify that `b` is an `R`-minimal element, we have `isMinimal R b` - the `Set.univ` is used implicitly. If we want to specify that `b` is a minimal element of a subset `B` of `u`, write `isMinimal R b B` - in this case, `B` overrides `Set.univ`. -/
DefinitionDoc isMinimal as "REL: isMinimal"

/-- If `R` is a relation on `u`, `isMaximal R b` means that `b` is a maximal element of `u`. In Lean,
```
isMaximal
{u : Type*}
(R: Rel_on u)
(b : u)
(B : Set u := Set.univ) :=
  b ∈ B ∧ ∀ x, x ∈ B → R b x → x = b
```
The statement `B : Set u := Set.univ` means that the *default value* passed to `isMaximal` for that argument is `Set.univ`. So, if we want to specify that `b` is an `R`-maximal element, we have `isMaximal R b` - the `Set.univ` is used implicitly. If we want to specify that `b` is a maximal element of a subset `B` of `u`, write `isMaximal R b B` - in this case, `B` overrides `Set.univ`. -/
DefinitionDoc isMaximal as "REL: isMaximal"

/-- If `R` is a relation on `u`, `isSmallest R b` means that `b` is the smallest element of `u`. In Lean,
```
isSmallest
{u : Type*}
(R: Rel_on u)
(b : u)
(B : Set u := Set.univ) :=
  b ∈ B ∧ ∀ x, x ∈ B → R b x
```
The statement `B : Set u := Set.univ` means that the *default value* passed to `isSmallest` for that argument is `Set.univ`. So, if we want to specify that `b` is the `R`-smallest element, we have `isSmallest R b` - the `Set.univ` is used implicitly. If we want to specify that `b` is the smallest element of a subset `B` of `u`, write `isSmallest R b B` - in this case, `B` overrides `Set.univ`. -/
DefinitionDoc isSmallest as "REL: isSmallest"

/-- If `R` is a relation on `u`, `isLargest R b` means that `b` is the largest element of `u`. In Lean,
```
isLargest
{u : Type*}
(R: Rel_on u)
(b : u)
(B : Set u := Set.univ) :=
  b ∈ B ∧ ∀ x, x ∈ B → R x b
```
The statement `B : Set u := Set.univ` means that the *default value* passed to `isLargest` for that argument is `Set.univ`. So, if we want to specify that `b` is the `R`-largest element, we have `isLargest R b` - the `Set.univ` is used implicitly. If we want to specify that `b` is the largest element of a subset `B` of `u`, write `isLargest R b B` - in this case, `B` overrides `Set.univ`.  -/
DefinitionDoc isLargest as "REL: isLargest"

/-- If `R` is a relation on `u`, `isUpperBound R b` means that `b` is an upper bound of `u`. In Lean,
```
isUpperBound
{u : Type*}
(R: Rel_on u)
(b : u)
(B : Set u := Set.univ) :=
  ∀ x, x ∈ B → R x b
```
The statement `B : Set u := Set.univ` means that the *default value* passed to `isUpperBound` for that argument is `Set.univ`. So, if we want to specify that `b` is an `R`-upper bound, we have `isUpperBound R b` - the `Set.univ` is used implicitly. If we want to specify that `l` is an upper bound of a subset `B` of `u`, write `isUpperBound R b B` - in this case, `B` overrides `Set.univ`. -/
DefinitionDoc isUpperBound as "REL: isUpperBound"

/-- If `R` is a relation on `u`, `isLowerBound R b` means that `b` is a lower bound of `u`. In Lean,
```
isLowerBound
{u : Type*}
(R: Rel_on u)
(l : u)
(B : Set u := Set.univ) :=
  ∀ x, x ∈ B → R l x
```
The statement `B : Set u := Set.univ` means that the *default value* passed to `isLowerBound` for that argument is `Set.univ`. So, if we want to specify that `l` is an `R`-lower bound, we have `isLowerBound R l` - the `Set.univ` is used implicitly. If we want to specify that `l` is a lower bound of a subset `B` of `u`, write `isLowerBound R l B` - in this case, `B` overrides `Set.univ`. -/
DefinitionDoc isLowerBound as "REL: isLowerBound"

/-- If `R` is a relation on `u`, `isInfimum R l B` means that `l` is the greatest lower bound for the subset `B` of `u`. To work with the greatest lower bound, we need to define the set of lower bounds - this is called `LowerBounds`:
```
LowerBounds
{u : Type*}
(R : Rel_on u)
(B : Set u := Set.univ) :=
  {l | isLowerBound R l B}
```
With this, we can define `isInfimum`:
```
isInfimum
{u : Type*}
(R: Rel_on u)
(l : u)
(B : Set u := Set.univ) :=
  isLargest R l (LowerBounds R B)
```
Unpacking the definitions, `h : isInfimum R l B` means `l ∈ LowerBounds R B ∧ ∀ x, x ∈ (LowerBounds R B) → R x l`.
-/
DefinitionDoc isInfimum as "REL: isInfimum"

/-- If `R` is a relation on `u`, `isSupremum R l B` means that `s` is the least upper bound for the subset `B` of `u`. To work with the least upper bound we need to define the set of upper bounds - this is called `UpperBounds`:
```
UpperBounds
{u : Type*}
(R : Rel_on u)
(B : Set u := Set.univ) :=
  {s | isUpperBound R s B}
```
With this, we can define `isSuprmum`:
```
isSupremum
{u : Type*}
(R: Rel_on u)
(s : u)
(B : Set u := Set.univ) :=
  isSmallest R s (UpperBounds R B)
```
Unpacking the definitions, `h : isSupremum R s B` means `s ∈ UpperBounds R B ∧ ∀ x, x ∈ (UpperBounds R B) → R s x`. -/
DefinitionDoc isSupremum as "REL: isSupremum"

/-- `subsetOrder u` is the subset order relation on a type `u`. If `A` and `B` are sets of elements of `u` , then `(subsetOrder u) A B` is a fancy way of writing `A ⊆ B`.-/
DefinitionDoc subsetOrder as "REL: subsetOrder"

/-- If `R` is an equivalence relation on `u`, `equivClass R a` is the equivalence class of `a : u`; that is, `equivClass R a = { b | R a b}`.-/
DefinitionDoc equivClass as "REL: equivClass"


/--
This is the proof that `a ∈ equivClass R a`; more precisely,
```
Equiv_class_has_rep
{u : Type*}
(R: Rel_on u)
(eq: isEquivalence R)
(a : u) :
  a ∈ equivClass R a
```
To use this, notice that you have to tell Lean that your relation is an equivalence relation.
-/
TheoremDoc Equiv_class_has_rep as "REL: Equiv_class_has_rep"

/--
This is the proof that equivalence classes are "representative-independent"; you may choose any element of an element's equivalence class as the class's representative. This is very useful in equivalence relation proofs.
```
Equiv_class_rep_ind
{u : Type*}
(R: Rel_on u)
(eq: isEquivalence R)
(a b: u)
(h: b ∈ EquivClass R a) :
  equivClass R a = equivClass R b
```
-/
TheoremDoc Equiv_class_rep_ind as "REL: Equiv_class_rep_ind"

/-- If `R` is an equivalence relation on type `u`, `equivClassFamily R` is the set of equivalence classes of `R`; that is, `{ equivClass R a | a : u}`.
-/
DefinitionDoc equivClassFamily as "REL: equivClassFamily"


/--
An ordered pair `(a,b)` fails to be in the Cartesian product `A ×ˢ B` as long as `b ∉ B`. In Lean,
```
Snd_not_mem_not_mem_prod
{u v: Type*}
(A: Set u)
(B: Set v)
(x : u)
(y: v)
(h: y ∉ B) :
  (x,y) ∉ (A ×ˢ B)
```
-/
TheoremDoc Snd_not_mem_not_mem_prod as "REL: Snd_not_mem_not_mem_prod"

/-- `Rel_union R S` is the "union" of the relations `R` and `S`. The Lean definition needs a `fun` to explicitly describe the relation:
```
Rel_union
{u v : Type*}
(R S : Rel u v) :
  Rel u v := fun a b => R a b ∨ S a b
``` -/
DefinitionDoc Rel_union as "REL: Rel_union"
