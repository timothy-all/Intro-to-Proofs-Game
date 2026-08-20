import GameServer

/--
This helps to define the `Δ` (symmetric difference) operator on sets. Specifically,

$$
A \mathop{Δ} B  = (A \ B) ∪ (B \ A)
$$

So `mem_symm_diff_iff` says specifically that `x ∈ A Δ B ↔ x ∈ (A \ B) ∨ (x ∈ B \ A)`. Here's what it looks like in Lean:
```
mem_symm_diff_iff
  {u : Type*}
  {x : u}
  (A B : Set u) :
  x ∈ (A Δ B) ↔ x ∈ (A \ B) ∪ (B \ A)
```
-/
DefinitionDoc mem_symm_diff_iff as "SET: mem_symm_diff_iff"


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
The symmetric difference between a set and itself is the empty set.
-/
TheoremDoc Symm_diff_self as "SET : Symm_diff_self"
