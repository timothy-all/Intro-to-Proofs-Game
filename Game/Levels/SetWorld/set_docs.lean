import GameServer

/--
This helps to define the `∩` set connective. Specifically,
```
A ∩ B = {x | x ∈ A ∧ x ∈ B}
```
So `mem_inter_iff` says specifically that `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`. Here's how it looks in Lean:
```
mem_inter_iff
  {u : Type*}
  (x : u)
  (a b : Set u) :
    x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b
```
Here's a Venn diagram of the `∩` connective:
![Venn diagram of union connective](images/venn_inter.png)
-/
DefinitionDoc Set.mem_inter_iff as "SET: mem_inter_iff"

/--
This helps to define the `∪` set connective. Specifically,
```
A ∪ B = {x | x ∈ A ∨ x ∈ B}
```
So `mem_union_iff` says specifically that `x ∈ A ∩ B ↔ x ∈ A ∨ x ∈ B`. Here's how it looks in Lean:
```
mem_inter_iff
  {u : Type*}
  (x : u)
  (a b : Set u) :
    x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b
```
Here's a Venn diagram of the `∪` connective:
![Venn diagram of union connective](images/venn_union.png)
-/
DefinitionDoc mem_union_iff as "SET: mem_union_iff"


/--
This helps to define the `ᶜ` (complement) unary operator on sets. Specifically,
```
Aᶜ = { x | x ∉ A}
```
So `mem_compl_iff` says specifically that `x ∈ Aᶜ ↔ x ∉ A`. Here's what it looks like in Lean:
```
mem_compl_iff
  (u : Type*}
  (s : Set u)
  (x : u) :
    x ∈ sᶜ ↔ x ∉ s
```
-/
DefinitionDoc Set.mem_compl_iff as "SET: mem_compl_iff"

/--
This helps to define the `\` set connective. Specifically,
```
A \ B = {x | x ∈ A ∧ x ∉ B}
```
So `mem_diff_iff` says specifically that `x ∈ A \ B ↔ x ∈ A ∧ x ∉ B`. Here's how it looks in Lean:
```
mem_inter_iff
  {u : Type*}
  (x : u)
  (a b : Set u) :
    x ∈ a \ b ↔ x ∈ a ∧ x ∉ b
```
-/
DefinitionDoc mem_diff_iff as "SET: mem_diff_iff"

/--
This helps to define the `=` relation between sets. We say that two sets `A B` are equal to mean that for every `x : u`, `x ∈ A` if and only if `x ∈ B`. Here's what it looks like in Lean:
```
set_eq_iff
  (u : Type*}
  (A B : Set u)
    A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
```
-/
DefinitionDoc set_eq_iff as "SET: set_eq_iff"

/--
This helps to define the `⋂₀` (intersection of families) operator on a family of sets. Specifically,

$$
⋂₀ F = ⋂_{t ∈ F} t
$$

So `mem_finter_iff` says specifically that `x ∈ ⋂₀ F ↔ ∀ (t : Set u), t ∈ F → x ∈ t`. Here's what it looks like in Lean:
```
mem_finter_iff
  {u : Type*}
  {x : u}
  (F : Set (Set u)) :
  x ∈ ⋂₀ F ↔ ∀ (t : Set u), t ∈ F → x ∈ t
```
-/
DefinitionDoc mem_finter_iff as "SET: mem_finter_iff"

/--
This helps to define the `⋂` (intersection of indexed sets) operator on an indexed family of sets. Specifically,

$$
⋂ i, A i  = ⋂_{i ∈ I} A_i
$$

So `mem_iinter_iff` says specifically that `x ∈ ⋂ i, A i ↔ ∀ (i : I), x ∈ A i`. Here's what it looks like in Lean:
```
mem_iinter_iff
  {u : Type*}
  {x : u}
  {I : Type*}
  (A : I → Set u) :
    x ∈ ⋂ i, A i ↔ ∀ (i : I), x ∈ A i
```
-/
DefinitionDoc mem_iinter_iff as "SET: mem_iinter_iff"

/--
This helps to define the `⋃₀` (intersection of families) operator on a family of sets. Specifically,

$$
⋃₀ F = ⋃_{t ∈ F} t
$$

So `mem_funion_iff` says specifically that `x ∈ ⋃₀ F ↔ ∃ t ∈ F, x ∈ t`. Here's what it looks like in Lean:
```
mem_funion_iff
  {u : Type*}
  {x : u}
  (F : Set (Set u)) :
    x ∈ ⋃₀ F ↔ ∃ t ∈ F, x ∈ t
```
-/
DefinitionDoc mem_funion_iff as "SET: mem_funion_iff"

/--
This helps to define the `⋃` (intersection of indexed sets) operator on an indexed family of sets. Specifically,

$$
⋃ i, A i  = ⋃_{i ∈ I} A_i
$$

So `mem_iunion_iff` says specifically that `x ∈ ⋃ i, A i ↔ ∃ (i : I), x ∈ A i`. Here's what it looks like in Lean:
```
mem_iunion_iff
  {u : Type*}
  {x : u}
  {I : Type*}
  (A : I → Set u) :
    x ∈ ⋃ i, A i ↔ ∃ (i : I), x ∈ A i
```
-/
DefinitionDoc mem_iunion_iff as "SET : mem_iunion_iff"

/--
This helps to define the `∅`, the empty set. Specifically,

$$
∅ = {x : u | False}
$$

So `mem_empty_iff_false` says specifically that `x ∈ ∅ ↔ False`. Here's what it looks like in Lean:
```
mem_empty_iff_false
  {u : Type*}
  (x : u) :
    x ∈ ∅ ↔ False
```
-/
DefinitionDoc Set.mem_empty_iff_false as "SET: mem_empty_iff_false"

/--
This helps to define the `univ`, the set consisting of everything. Specifically,

$$
univ = {x : u | True}
$$

So `mem_univ_iff_true` says specifically that `x ∈ univ ↔ True`. Here's what it looks like in Lean:
```
mem_univ_iff_True
  {u : Type*}
  (x : u) :
    x ∈ univ ↔ True
```
-/
DefinitionDoc mem_univ_iff_true as "SET: mem_univ_iff_true"

/--
This helps to define `𝒫 A`, the power set of `A`. Specifically,

$$
𝒫 A = {B : Set u | B ⊆ A}
$$

So `mem_powerset_iff` says specifically that `B ∈ 𝒫 A ↔ B ⊆ A`. Here's what it looks like in Lean:
```
mem_powerset_iff
  {u : Type*}
  (x s : Set u) :
    x ∈ 𝒫 s ↔ x ⊆ s
```
-/
DefinitionDoc Set.mem_powerset_iff as "SET: mem_powerset_iff"

/--
This helps to define `⊆` relation. Specifically, $A ⊆ B$ means

$$
∀ x, x ∈ A → x ∈ B
$$

So `subset_iff` says specifically that `A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B`. Here's what it looks like in Lean:
```
subset_iff
  {u : Type*}
  {A B : Set u} :
    A ⊆ B ↔ ∀ {x}, x ∈ A → x ∈ B
```
Here's a Venn diagram of the `⊆` relation:
![Venn diagram of union connective](images/venn_subset.png)
-/
DefinitionDoc subset_iff as "SET: subset_iff"


/--
The relation `⊆` between sets is *transitive* meaning that if `A ⊆ B` and `B ⊆ C`, then `A ⊆ C`.
-/
TheoremDoc Subseteq_trans as "SET: Subseteq_trans"
