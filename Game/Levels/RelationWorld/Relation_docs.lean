import GameServer


/--
This is the **set** Cartesian product symbol, used in set Cartesian product levels found in RelationWorld and RelationWorldExamples. So, if `A` is a set of elements from type `u` and `B` is a set of elements from type `v` (in Lean: `A : Set u`, `B: Set v`), ```
A ×ˢ B = { (a,b) | a ∈ A ∧ b ∈ B}.
```
If `p ∈ A ×ˢ B`, you can access the coordinates of `p` by using `p.1` and `p.2` (or `p.fst` and `p.snd` - first and second).

To type this symbol, write `\xs`.
-/
DefinitionDoc Set.prod as "REL: ×ˢ"


/--
This tells us what it means to be a member of the Cartesian product of two **sets**. Here's how it looks in Lean:
```
Mem_prod
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
TheoremDoc Mem_prod as "REL: Mem_prod"


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


/-- `R.inv` is the inverse of the relation `R`. More precisely, `R a b` if and only if `R.inv b a`. --/
DefinitionDoc Rel.inv as "REL: Rel.inv"


/-- The inverse of the inverse of a relation is itself. In Lean,
```
Rel_inv_inv
{u v : Type}
(R: Rel u v) :
  (R.inv).inv = R
```
-/
TheoremDoc Rel_inv_inv as "REL: Rel_inv_inv"

/-- `R.dom` is the domain of the relation `R`. This is a **set**:
```
R.dom = { a | ∃ b, R a b }
```
-/
DefinitionDoc Rel.dom as "REL: Rel.dom"

/-- `R.range` is the range of the relation `R`. This is a **set**:
```
R.range = { b | ∃ a, R a b }
``` --/
DefinitionDoc Rel.range as "REL: Rel.range"

/-- `Rel_on u` is shorthand for `Rel u u`.
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

/--Replaces the `set` of the identity relation on `u` with the more concrete set of ordered pairs of the form `(a,a)`.-/
TheoremDoc Rel_id_set as "REL: Rel_id_set"



/-- Makes a relation `R` reflexive. -/
DefinitionDoc isReflexive as "REL: isReflexive"

/-- Makes a relation `R` symmetric. -/
DefinitionDoc isSymmetric as "REL: isSymmetric"

/-- Makes a relation `R` anti-symmetric. -/
DefinitionDoc isAntisymmetric as "REL: isAntiymmetric"

/-- Makes a relation `R` transitive. -/
DefinitionDoc isTransitive as "REL: isTransitive"

/-- Makes a relation `R` an equivalence relation. -/
DefinitionDoc isEquivalence as "REL: isEquivalence"

/-- Makes a relation `R` a partial order. If `po: isPartialOrder R`, use `po.refl`, `po.anti`, `po.tran` to access the reflexive, anti-symmetric, and transitive properties, respectively. -/
DefinitionDoc isPartialOrder as "REL: isPartialOrder"

/-- If `R` is a relation on `u`, `isMinimal R b` means that `b` is a minimal element of `u`.

If we want to specify that `b` is a minimal element of a subset `B` of `u`, write `isMinimal R b B`. -/
DefinitionDoc isMinimal as "REL: isMinimal"

/-- If `R` is a relation on `u`, `isMaximal R b` means that `b` is a maximal element of `u`.

If we want to specify that `b` is a maximal element of a subset `B` of `u`, write `isMaximal R b B`. -/
DefinitionDoc isMaximal as "REL: isMaximal"

/-- If `R` is a relation on `u`, `isSmallest R b` means that `b` is the smallest element of `u`.

If we want to specify that `b` is the smallest element of a subset `B` of `u`, write `isSmallest R b B`. -/
DefinitionDoc isSmallest as "REL: isSmallest"

/-- If `R` is a relation on `u`, `isLargest R b` means that `b` is the largest element of `u`.

If we want to specify that `b` is the largest element of a subset `B` of `u`, write `isLargest R b B`. -/
DefinitionDoc isLargest as "REL: isLargest"

/-- If `R` is a relation on `u`, `isLowerBound R l B` means that `l` is a lower bound for the subset `B` of `u`. -/
DefinitionDoc isLowerBound as "REL: isLowerBound"

/-- If `R` is a relation on `u`, `isUpperBound R s B` means that `u` is an upper bound for the subset `B` of `u`. -/
DefinitionDoc isUpperBound as "REL: isUpperBound"

/-- If `R` is a relation on `u`, `isInfimum R l B` means that `l` is the greatest lower bound for the subset `B` of `u`. -/
DefinitionDoc isInfimum as "REL: isInfimum"

/-- If `R` is a relation on `u`, `isSupremum R s B` means that `s` is the least upper bound for the subset `B` of `u`. -/
DefinitionDoc isSupremum as "REL: isSupremum"

/-- `subsetOrder u` is the subset order relation on a type `u`. If `A` and `B` are sets of elements of `u` , then `(subsetOrder u) A B` is a fancy way of writing `A ⊆ B`.-/
DefinitionDoc subsetOrder as "REL: subsetOrder"

/-- If `R` is an equivalence relation on `u`, `equivClass R a` is the equivalence class of `a : u`; that is, `equivClass R a = { b | R a b}`.-/
DefinitionDoc equivClass as "REL: equivClass"


/-- This is the proof that `a ∈ equivClass R a`; more precisely,
```
Equiv_class_has_rep
{u : Type*}
(R: Rel_on u)
(eq: isEquivalence R)
(a : u) :
  a ∈ equivClass R a
```
To use this, notice that you have to tell Lean that your relation is an equivalence relation. -/
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
